;;; Simplified miniKanren interpreter in Scheme
;;;
;;; Original version written in the style of Indiana University's C311/B521 courses
;;; by Jason Hemann, Dan Friedman, and Will Byrd
;;;
;;; Modified by Will Byrd on 8 July 2016 to use a simplified
;;; language---sort of a mashup of miniKanren and microKanren.

(load "pmatch.scm")

;; The following conventions are often used in the following
;; <g>* indicates a list of <g>
;; <g>*s indicates a matrix of <g>, (really a list of <g>*)
;; ge indicates a goal expression, when evaluated, it's simply a g (goal)

(define ext-env*
  (lambda (x* a* env)
    `((env ,x* . ,a*) ,env)))

(define ext-rec-env*
  (lambda (x* a* env)
    `((rec-env ,x* . ,a*) ,env)))

(define apply-env
  (lambda (env x)
    (pmatch env
      (() (errorf 'apply-env "not in env ~s" x))
      (((env ,y* . ,a*) ,env^) (guard (memq x y*))
       (apply-rib y* a* x))
      (((rec-env ,y* . ,a*) ,env^) (guard (memq x y*))
       (let ((lam-exp (apply-rib y* a* x)))
         (pmatch lam-exp
           ((internal-use-lambda ,x* ,body-goal) (guard (for-all symbol? x*))
            (lambda (a*)
              (let ((env (ext-env* x* a* env)))
                (eval-goal-exp body-goal env)))))))
      (else (apply-env (cadr env) x)))))

(define apply-rib
  (lambda (y* a* x)
    (pmatch y*
      ((,y . ,y*) (guard (eq? y x)) (car a*))
      (else (apply-rib (cdr y*) (cdr a*) x)))))

(define-syntax lambdag@
  (syntax-rules ()
    ((_ (a) e) (lambda (a) (lambdaf@ () e)))))

(define-syntax lambdaf@
  (syntax-rules ()
    ((_ () e) (lambda () e))))

(define value-of
  (lambda (prog)
    (eval-prog prog '())))

(define eval-prog
  (lambda (prog env)
    (pmatch prog
      ((begin . ,def*/body)
       (begin-aux def*/body env))
      ((run ,nexp (,x) . ,ge*) (guard (symbol? x))
       (eval-run-exp prog env))
      (else (error 'eval-prog "Invalid prog" prog)))))

(define eval-run-exp
  (lambda (run-exp env)
    (pmatch run-exp
      ((run ,nexp (,x) . ,ge*) (guard (symbol? x))
       (let ((n (eval-simple-exp nexp env))
             (x-var (var x)))
         (let ((env^ (ext-env* `(,x) `(,x-var) env)))
           (let ((g (conj (eval-goal-exp* ge* env^))))
             (let ((a* (take n (lambdaf@ () (g '())))))
               (map (reify x-var) a*))))))
      (else (error 'eval-run-exp "Invalid run-exp" run-exp)))))

(define eval-simple-exp
  (lambda (exp env)
    (pmatch exp
      (,b (guard (boolean? b)) b)
      (,x (guard (symbol? x)) (apply-env env x))
      (,n (guard (number? n)) n)      
      ((quote ,val) val)
      ((cons ,e1 ,e2) (cons (eval-simple-exp e1 env) (eval-simple-exp e2 env)))
      (else (error 'eval-simple-exp "Invalid exp" exp)))))

(define eval-goal-exp
  (lambda (goal-exp env)
    (pmatch goal-exp
      ((== ,u ,v)
       (lambda (s)
         (lambdaf@ ()
           (let ((u (eval-simple-exp u env))
                 (v (eval-simple-exp v env)))
             (cond
               ((unify u v s) => unit)
               (else (mzero)))))))
      ((conj . ,ge*)
       (lambda (s)
         ((conj (eval-goal-exp* ge* env)) s)))
      ((disj . ,ge*)
       (lambda (s)
         ((disj (eval-goal-exp* ge* env)) s)))
      ((fresh ,x* ,ge) (guard (for-all symbol? x*))
       (let ((env^ (ext-env* x* (map var x*) env)))
         (lambda (s)
           ((conj (eval-goal-exp* (list ge) env^)) s))))
      ((,rator . ,rand*) (guard (symbol? rator))
       ;; since we got rid of user-level 'lambda', rator must be a
       ;; symbol that evaluates to a goal
       ((eval-simple-exp rator env) (eval-simple-exp* rand* env)))
      (else (error 'eval-goal-exp "Invalid goal-exp" goal-exp)))))

(define eval-goal-exp*
  (lambda (goal-exp* env)
    (map (lambda (ge) (eval-goal-exp ge env)) goal-exp*)))

(define eval-simple-exp*
  (lambda (exp* env)
    (map (lambda (e) (eval-simple-exp e env)) exp*)))

(define begin-aux
  (lambda (def*/body env)
    (letrec ((begin-aux
              (lambda (def*/body name* fn* env)
                (pmatch def*/body
                  (((run ,nexp (,x) . ,ge*)) (guard (symbol? x))
                   (let ((env^ (ext-rec-env* (reverse name*) (reverse fn*) env)))
                     (eval-run-exp (car def*/body) env^)))
                  (((define (,name . ,x*) ,e) . ,rest) (guard (for-all symbol? x*))
                   (begin-aux rest (cons name name*) (cons `(internal-use-lambda ,x* ,e) fn*) env))
                  (else (error 'begin-aux "Invalid def*/run" def*/body))))))
      (begin-aux def*/body '() '() env))))


;;; Helpers for miniKanren.

(define disj
  (lambda (g*)
    (lambda (s)
      (cond
        ((null? g*) (mzero))
        (else (mplus ((car g*) s)
                     (lambdaf@ () ((disj (cdr g*)) s))))))))

(define conj
  (lambda (g*)
    (lambda (s)
      (cond
        ((null? g*) (unit s))
        (else (bind ((car g*) s) (conj (cdr g*))))))))

(define bind
  (lambda (a-inf g)
    (cond
      ((null? a-inf) (mzero))
      ((procedure? a-inf) (lambdaf@ () (bind (a-inf) g)))
      (else ((let ((a (car a-inf)) (f (cdr a-inf)))
               (mplus (g a) (lambdaf@ () (bind (f) g)))))))))

(define mplus
  (lambda (a-inf f)
    (cond
      ((null? a-inf) (f))
      ((procedure? a-inf) (lambdaf@ () (mplus (f) a-inf)))
      (else (let ((a (car a-inf)) (f (lambdaf@ () (mplus (f) (cdr a-inf)))))
              (choice a f))))))

(define var 
  (lambda (c)
    (vector c)))

(define var?
  (lambda (x)
    (vector? x)))

(define walk
  (lambda (u S)
    (cond
      ((and (var? u) (assq u S)) =>
       (lambda (pr) (walk (cdr pr) S)))
      (else u))))

(define ext-s
  (lambda (x v s)
    (cons `(,x . ,v) s)))

(define unify
  (lambda (u v s)
    (let ((u (walk u s))
          (v (walk v s)))
      (cond
        ((and (var? u) (var? v) (eq? u v)) s)
        ((var? u) (ext-s-check u v s))
        ((var? v) (ext-s-check v u s))
        ((and (pair? u) (pair? v))
         (let ((s (unify (car u) (car v) s)))
           (and s (unify (cdr u) (cdr v) s))))
        ((equal? u v) s)
        (else #f)))))

(define ext-s-check
  (lambda (x v s)
    (cond
      ((occurs-check x v s) #f)
      (else (ext-s x v s)))))

(define occurs-check
  (lambda (x v s)
    (let ((v (walk v s)))
      (cond
        ((var? v) (eq? v x))
        ((pair? v) 
         (or  (occurs-check x (car v) s)
              (occurs-check x (cdr v) s)))
        (else #f)))))

(define mzero (lambdaf@ () '())) 

(define unit (lambdag@ (a) (cons a mzero)))

(define choice (lambda (a f) (cons a f)))

(define take
  (lambda (n f)
    (cond
      ((and n (zero? n)) '())
      (else (let ((a-inf (f)))
              (cond
                ((null? a-inf) '())
                ((procedure? a-inf) (take n a-inf))
                (else (cons (car a-inf)
                        (take (and n (sub1 n)) (cdr a-inf))))))))))

(define walk*
  (lambda (w s)
    (let ((v (walk w s)))
      (cond
        ((var? v) v)
        ((pair? v)
         (cons (walk* (car v) s) (walk* (cdr v) s)))
        (else v)))))

(define reify-s
  (lambda (v s)
    (let ((v (walk v s)))
      (cond
        ((var? v)
         (ext-s v (reify-name (length s)) s))
        ((pair? v) (reify-s (cdr v)
                     (reify-s (car v) s)))
        (else s)))))

(define reify-name
  (lambda (n)
    (string->symbol
      (string-append "_" "." (number->string n)))))

(define reify
  (lambda (v)
    (lambda (s)
      (let ((v (walk* v s)))
        (walk* v (reify-s v '()))))))


;;; tests
(define-syntax test-check
  (syntax-rules ()
    ((_ title tested-expression expected-result)
     (begin
       (printf "Testing ~s\n" title)
       (let* ((expected expected-result)
              (produced tested-expression))
         (or (equal? expected produced)
             (errorf 'test-check
               "Failed: ~a~%Expected: ~a~%Computed: ~a~%"
               'tested-expression expected produced)))))))


(test-check "run-g 0"
  (value-of '(run 1 (x) (== x 5)))
  '(5))

(test-check "unify constants"
  (value-of '(run #f (q) (== 5 7)))
  '())

(test-check "succeed"
  (value-of '(run #f (q) (== #f #f))) 
  '(_.0))

(test-check "second"
  (value-of '(run 2 (q)
               (== 5 q)))
  '(5))

(test-check "success of one goal"
  (value-of '(run 1 (q) (== q q)))
  '(_.0))

(test-check "ground success of one goal"
  (value-of '(run 1 (q) (== 5 q)))
  '(5))

(test-check "success of both branches in a run 1"
  (value-of '(run 1 (q)
               (fresh (j)
                 (conj
                   (== q q)
                   (== 5 5)))))
  '(_.0))

(test-check "first"
  (value-of '(run 1 (q)
               (fresh (x)
                 (== x q))))
  '(_.0))

(test-check "fresh (n*)"
  (value-of '(run 1 (q)
               (fresh (a b c)                  
                 (== (cons a (cons b (cons c '()))) q))))
  '((_.0 _.1 _.2)))

(test-check "fresh-3a"
  (value-of '(run 1 (q)
               (fresh (a b)
                 (conj
                   (== b 7)                       
                   (== q (cons a (cons b '())))
                   (== a 5)))))
  '((5 7)))

(test-check "fresh-3b"
  (value-of '(run 1 (q)
               (fresh (a b)
                 (conj
                   (== a 5)
                   (== b 7)
                   (== q (cons a (cons b '())))))))
  '((5 7)))

(test-check "fresh-3c"
  (value-of '(run 1 (q)
               (fresh (a b)
                 (conj
                  (== q (cons a (cons b '())))
                  (== b 7) (== a 5)))))
  '((5 7)))

(test-check "fresh n*0"
  (value-of '(run 1 (q)
               (fresh (a b c)
                 (conj
                   (== q (cons a (cons b (cons c '()))))                  
                   (== b 7)
                   (== c 7)
                   (== a 5)))))
  '((5 7 7)))

(test-check "fresh n*1"
  (value-of '(run 1 (q)
               (fresh (a b c)
                 (conj
                   (== q (cons a (cons b (cons c '()))))                  
                   (== b 7)
                   (== c 6)
                   (== a 5)))))
  '((5 7 6)))

(test-check "fresh n*2"
  (value-of '(run 1 (q)
               (fresh (a b c)
                 (conj
                   (== b 7)
                   (== q (cons a (cons b (cons c '()))))
                   (== c 6)
                   (== a 5)))))
  '((5 7 6)))

(test-check "fresh n*3"
  (value-of '(run 1 (q)
               (fresh (a b c)
                 (conj
                   (== b 7)
                   (== c 6)                  
                   (== q (cons a (cons b (cons c '()))))
                   (== a 5)))))
  '((5 7 6)))

(test-check "fresh n*4"
  (value-of '(run 1 (q)
               (fresh (a b c)
                 (conj
                   (== b 7)                          
                   (== c 6)
                   (== a 5)                                
                   (== q (cons a (cons b (cons c '()))))))))
  '((5 7 6)))

(test-check "fresh works"
  (value-of '(run 1 (x)
               (fresh (y z)
                 (== x (cons y (cons z '()))))))
  '((_.0 _.1)))

(test-check "fresh worksb"
  (value-of '(run 1 (x)
               (fresh (y z)
                 (conj
                   (== y 5)
                   (== z y)
                   (== x (cons y (cons z '())))))))
  '((5 5)))

(test-check "same goals in a fresh"
  (value-of '(run 4 (q)
               (fresh (a b)
                 (conj
                   (== a 4)                        
                   (== b 6)
                   (== a 4)                        
                   (== b 6)
                   (== (cons a (cons b '())) q)))))
  '((4 6)))

(test-check "distinct vars"
  (value-of
   '(run #f (q)
      (fresh (j)
        (conj
          (== q j)
          (== #f #f)))))
  '(_.0))

(test-check "failure of both branches"
  (value-of '(run 1 (q)
               (fresh (j)
                 (conj (== q q) (== 5 6)))))
  '())

(test-check "run-g 1"
  (value-of '(run #f (x)
               (disj
                 (== x 5)
                 (== x 6))))
  '(6 5))

(test-check "run-g 2"
  (value-of '(run 2 (x)
               (disj
                 (conj (== x 5))
                 (conj (== x 6)))))
  '(6 5))

(test-check "run*"
  (value-of '(run #f (x)
               (disj
                 (conj (== x 5))                 
                 (conj (== x 6)))))
  '(6 5))

;; (test-check "disj-true"
;;   (value-of '(run 1 (q) (disj (conj))))
;;   '(_.0))

(test-check "disj-false"
  (value-of '(run 1 (q) (disj)))
  '())

(test-check "disj 3"
  (value-of '(run 4 (q)
               (disj
                 (conj (== q 3))                 
                 (conj (disj
                         (conj (== q 6))                    
                         (conj (== q 4)))))))
  '(3 6 4))

(test-check "disj 3 b"
  (value-of '(run 4 (q)
               (disj
                 (== q 3)                 
                 (disj
                   (== q 6)                    
                   (== q 4)))))
  '(3 4 6))

(test-check "third"
  (value-of '(run 2 (q)
               (disj
                 (== 5 q)
                 (== 6 q))))
  '(6 5))

(test-check "run* 2 ans"
  (value-of '(run #f (q)
               (disj
                 (== 5 q)
                 (== 6 q))))
  '(6 5))

(test-check "four"
  (value-of '(run 3 (q)
               (disj
                 (== q 5)
                 (disj
                   (== q 6)
                   (== q 7)))))
  '(5 7 6))

(test-check "five"
  (value-of '(run #f (q)
               (disj
                 (== q 5)
                 (disj
                   (== q 6)
                   (== q 7)))))
  '(5 7 6))

(test-check "failure of one branch"
  (value-of '(run #f (q)
               (fresh (j)
                 (conj
                   (disj
                     (== q j)
                     (== 3 4))
                   (== #f #f)))))
  '(_.0))

(test-check "success of both branches"
  (value-of '(run #f (q)
               (fresh (j)
                 (conj
                   (disj
                     (== q j)
                     (== q j))
                   (== #f #f)))))
  '(_.0 _.0))

(test-check "ground success of both branches"
  (value-of '(run #f (q)
               (disj
                 (== q 3)
                 (== q 6))))
  '(6 3))

(test-check "breaking conde"
  (value-of '(run #f (q)
               (fresh (a b)                  
                 (disj
                   (conj
                     (disj
                       (== a 6)
                       (== a 5))
                     (== a q))
                   (== q 4)))))
  '(4 5 6))

(test-check "conde/fresh working"
  (value-of '(run #f (q)
               (fresh (a b)
                 (conj
                   (disj
                     (== a 4)
                     (disj
                       (== a 5)
                       (== a 6)))
                   (== b 7)
                   (== (cons a (cons b '())) q)))))
  '((4 7)
    (6 7)
    (5 7)))

(test-check "multiple runs through conde"
  (value-of '(run 4 (q)
               (fresh (a b)
                 (conj
                   (== (cons a (cons b '())) q)
                   (disj
                     (== a 4)                         
                     (disj
                       (== a 3)                            
                       (== a 5)))                          
                   (== b 4)))))
  '((4 4)
    (5 4)
    (3 4)))

(test-check "nested conde, basic"
  (value-of '(run 4 (q)
               (fresh (a b)
                 (conj
                   (disj
                     (== a 3)                        
                     (== a 4))                       
                   (== a q)))))
  '(4 3))

(test-check "nested conde"
  (value-of '(run 4 (q)
               (fresh (a b)
                 (conj
                   (disj
                     (== a 3)                         
                     (== a 4))                        
                   (== b 7)                                            
                   (== (cons a (cons b '())) q)))))
  '((4 7)
    (3 7)))

(test-check "12 answers"
  (value-of '(run #f (q)
               (fresh (a b)
                 (conj
                   (disj
                     (conj
                       (== b 0)
                       (disj
                         (== a 0)
                         (== a 1)
                         (== a 2)
                         (== a 3)))
                     (conj
                       (== b 1)
                       (disj
                         (== a 0)
                         (== a 1)
                         (== a 2)
                         (== a 3)))
                     (conj
                       (== b 2)
                       (disj
                         (== a 0)
                         (== a 1)
                         (== a 2)
                         (== a 3))))
                   (== (cons a (cons b '())) q)))))
  '((0 0) (1 0) (3 0) (2 0) (0 1) (0 2) (1 1) (1 2) (2 2) (3 1) (2 1) (3 2)))

(printf "******* FIXME -- commented test 'proper-listo'\n")
#|
(test-check "proper-listo"
  (value-of '(run 7 (q)
               (let ((f (lambda (f)
                          (lambda (q)
                            (conde
                              ((== q '()))                              
                              ((fresh (a d)                                
                                 (== (cons a d) q)
                                 ((f f) d))))))))
                 ((f f) q))))
  '(()
    (_.0)
    (_.0 _.1)
    (_.0 _.1 _.2)
    (_.0 _.1 _.2 _.3)
    (_.0 _.1 _.2 _.3 _.4)
    (_.0 _.1 _.2 _.3 _.4 _.5)))
|#

(printf "******* FIXME -- commented test 'curried appendo'\n")
#|
(test-check "curried appendo"
  (value-of '(run 10 (q)
               (fresh (a b c)
                 (== (cons a (cons b (cons c '()))) q)
                 (let ((f (lambda (f)
                            (lambda (x)
                              (lambda (y)
                                (lambda (z)
                                  (conde
                                    ((== '() x)
                                     (== y z))
                                    ((fresh (h i j)
                                       (== (cons h i) x)
                                       (== (cons h j) z)
                                       ((((f f) i) y) j))))))))))
                   ((((f f) a) b) c)))))
  '((() _.0 _.0)
    ((_.0) _.1 (_.0 . _.1))
    ((_.0 _.1) _.2 (_.0 _.1 . _.2))
    ((_.0 _.1 _.2) _.3 (_.0 _.1 _.2 . _.3))
    ((_.0 _.1 _.2 _.3) _.4 (_.0 _.1 _.2 _.3 . _.4))
    ((_.0 _.1 _.2 _.3 _.4) _.5 (_.0 _.1 _.2 _.3 _.4 . _.5))
    ((_.0 _.1 _.2 _.3 _.4 _.5) _.6 (_.0 _.1 _.2 _.3 _.4 _.5 . _.6))
    ((_.0 _.1 _.2 _.3 _.4 _.5 _.6) _.7 (_.0 _.1 _.2 _.3 _.4 _.5 _.6 . _.7))
    ((_.0 _.1 _.2 _.3 _.4 _.5 _.6 _.7) _.8 (_.0 _.1 _.2 _.3 _.4 _.5 _.6 _.7 . _.8))
    ((_.0 _.1 _.2 _.3 _.4 _.5 _.6 _.7 _.8) _.9 (_.0 _.1 _.2 _.3 _.4 _.5 _.6 _.7 _.8 . _.9))))
|#

(test-check "define proper listo"
  (value-of '(begin
               (define (proper-listo l)
                 (disj
                   (== l '())                                   
                   (fresh (a d)
                     (conj
                       (== (cons a d) l)
                       (proper-listo d)))))
               (run 7 (q)
                 (proper-listo q))))
  '(()
    (_.0)
    (_.0 _.1)
    (_.0 _.1 _.2)
    (_.0 _.1 _.2 _.3)
    (_.0 _.1 _.2 _.3 _.4)
    (_.0 _.1 _.2 _.3 _.4 _.5)))


(test-check "define uncurried appendo"
  (value-of '(begin
               (define (appendo l s o)
                 (disj
                   (fresh (a d)
                     (conj
                       (== (cons a d) l)
                       (fresh (res)
                         (conj
                           (appendo d s res)
                           (== (cons a res) o)))))
                   (conj (== l '()) (== s o))))
               (run 4 (q)
                 (fresh (a b c)
                   (conj
                     (appendo a b c)                            
                     (== (cons a (cons b (cons c '()))) q))))))
  '((() _.0 _.0)
    ((_.0) _.1 (_.0 . _.1))
    ((_.0 _.1) _.2 (_.0 _.1 . _.2))
    ((_.0 _.1 _.2) _.3 (_.0 _.1 _.2 . _.3))))

(test-check "define uncurried appendo the normal way"
  (value-of '(begin
               (define (appendo l s o)
                 (disj
                   (conj (== l '()) (== s o))
                   (fresh (a d)
                     (conj
                       (== (cons a d) l)
                       (fresh (res)
                         (conj
                           (appendo d s res)
                           (== (cons a res) o)))))))
               (run 4 (q)
                 (fresh (a b c)
                   (conj
                     (appendo a b c)
                     (== (cons a (cons b (cons c '()))) q))))))
  '((() _.0 _.0)
    ((_.0) _.1 (_.0 . _.1))
    ((_.0 _.1) _.2 (_.0 _.1 . _.2))
    ((_.0 _.1 _.2) _.3 (_.0 _.1 _.2 . _.3))))

(test-check "define *o"
  (value-of
   '(begin
      (define (zeroo n) (== '() n))
      (define (poso n) (fresh (a d) (== (cons a d) n)))
      (define (>1o n) (fresh (a ad dd) (== (cons a (cons ad dd)) n)))
      (define (full-addero b x y r c)
        (disj (conj (== 0 b) (== 0 x) (== 0 y) (== 0 r) (== 0 c))
              (conj (== 1 b) (== 0 x) (== 0 y) (== 1 r) (== 0 c))
              (conj (== 0 b) (== 1 x) (== 0 y) (== 1 r) (== 0 c))
              (conj (== 1 b) (== 1 x) (== 0 y) (== 0 r) (== 1 c))
              (conj (== 0 b) (== 0 x) (== 1 y) (== 1 r) (== 0 c))
              (conj (== 1 b) (== 0 x) (== 1 y) (== 0 r) (== 1 c))
              (conj (== 0 b) (== 1 x) (== 1 y) (== 0 r) (== 1 c))
              (conj (== 1 b) (== 1 x) (== 1 y) (== 1 r) (== 1 c))))
      (define (addero d n m r)
        (disj (conj (== 0 d) (== '() m) (== n r))
              (conj (== 0 d) (== '() n) (== m r) (poso m))
              (conj (== 1 d) (== '() m) (addero 0 n '(1) r))
              (conj (== 1 d) (== '() n) (poso m) (addero 0 '(1) m r))
              (conj (== '(1) n)
                    (== '(1) m)
                    (fresh (a c)
                      (conj
                        (== (cons a (cons c '())) r)
                        (full-addero d 1 1 a c))))
              (conj (== '(1) n) (gen-addero d n m r))
              (conj (== '(1) m) (>1o n) (>1o r) (addero d '(1) n r))
              (conj (>1o n) (gen-addero d n m r))))
      (define (gen-addero d n m r)
        (fresh (a b c e x y z)
          (conj
            (== (cons a x) n)
            (== (cons b y) m)
            (poso y)
            (== (cons c z) r)
            (poso z)
            (full-addero d a b c e)
            (addero e x y z))))
      (define (pluso n m k)
        (addero 0 n m k))
      (define (minuso n m k)
        (pluso m k n))
      (define (*o n m p)
        (disj (conj (== '() n) (== '() p))
              (conj (poso n) (== '() m) (== '() p))
              (conj (== '(1) n) (poso m) (== m p))
              (conj (>1o n) (== '(1) m) (== n p))
              (conj (fresh (x z)
                      (conj
                        (== (cons 0 x) n)
                        (poso x)
                        (== (cons 0 z) p)
                        (poso z)
                        (>1o m)
                        (*o x m z))))
              (conj (fresh (x y)
                      (conj
                        (== (cons 1 x) n)
                        (poso x)
                        (== (cons 0 y) m)
                        (poso y)
                        (*o m n p))))
              (conj (fresh (x y)
                      (conj
                        (== (cons 1 x) n)
                        (poso x)
                        (== (cons 1 y) m)
                        (poso y)
                        (odd-*o x n m p))))))
      (define (odd-*o x n m p)
        (fresh (q)
          (conj
            (bound-*o q p n m)
            (*o x m q)
            (pluso (cons 0 q) m p))))
      (define (bound-*o q p n m)
        (disj
          (conj (== '() q) (poso p))
          (conj
            (fresh (a0 a1 a2 a3 x y z)
              (conj
                (== (cons a0 x) q)
                (== (cons a1 y) p)
                (disj
                  (conj (== '() n) (== (cons a2 z) m) (bound-*o x y z '()))
                  (conj (== (cons a3 z) n) (bound-*o x y z m))))))))
      (define (=lo n m)
        (disj
          (conj (== '() n) (== '() m))
          (conj (== '(1) n) (== '(1) m))
          (conj
            (fresh (a x b y)
              (conj
                (== (cons a x) n)
                (poso x)
                (== (cons b y) m)
                (poso y)
                (=lo x y))))))
      (define (<lo n m)
        (disj
          (conj (== '() n) (poso m))
          (conj (== '(1) n) (>1o m))
          (conj
            (fresh (a x b y)
              (conj
                (== (cons a x) n)
                (poso x)
                (== (cons b y) m)
                (poso y)
                (<lo x y))))))
      (define (<=lo n m) (disj (conj (=lo n m)) (conj (<lo n m))))
      (define (<o n m)
        (disj
          (conj (<lo n m))
          (conj (=lo n m) (fresh (x) (conj (poso x) (pluso n x m))))))
      (define (<=o n m) (disj (conj (== n m)) (conj (<o n m))))
      (define (/o n m q r)
        (disj
          (conj (== r n) (== '() q) (<o n m))
          (conj (== '(1) q) (=lo n m) (pluso r m n) (<o r m))
          (conj
            (<lo m n)
            (<o r m)
            (poso q)
            (fresh (nh nl qh ql qlm qlmr rr rh)
              (conj
                (splito n r nl nh)
                (splito q r ql qh)
                (disj
                  (conj
                    (== '() nh)
                    (== '() qh)
                    (minuso nl r qlm)
                    (*o ql m qlm))
                  (conj
                    (poso nh)
                    (*o ql m qlm)
                    (pluso qlm r qlmr)
                    (minuso qlmr nl rr)
                    (splito rr r '() rh)
                    (/o nh m qh rh))))))))
      (define (splito n r l h)
        (disj (conj (== '() n) (== '() h) (== '() l))
              (conj
                (fresh (b n^)
                  (conj
                    (== (cons 0 (cons b n^)) n)
                    (== '() r)
                    (== (cons b n^) h)
                    (== '() l))))
              (conj
                (fresh (n^)
                  (conj
                    (== (cons 1 n^) n)
                    (== '() r)
                    (== n^ h)
                    (== '(1) l))))
              (conj
                (fresh (b n^ a r^)
                  (conj
                    (== (cons 0 (cons b n^)) n)
                    (== (cons a r^) r)
                    (== '() l)
                    (splito (cons b n^) r^ '() h))))
              (conj
                (fresh (n^ a r^)
                  (conj
                    (== (cons 1 n^) n)
                    (== (cons a r^) r)
                    (== '(1) l)
                    (splito n^ r^ '() h))))
              (conj
                (fresh (b n^ a r^ l^)
                  (conj
                    (== (cons b n^) n)
                    (== (cons a r^) r)
                    (== (cons b l^) l)
                    (poso l^)
                    (splito n^ r^ l^ h))))))
      (define (logo n b q r)
        (disj (conj (== '(1) n) (poso b) (== '() q) (== '() r))
              (conj (== '() q) (<o n b) (pluso r '(1) n))
              (conj (== '(1) q) (>1o b) (=lo n b) (pluso r b n))
              (conj (== '(1) b) (poso q) (pluso r '(1) n))
              (conj (== '() b) (poso q) (== r n))
              (conj (== '(0 1) b)
                    (fresh (a ad dd)
                      (conj
                        (poso dd)
                        (== (cons a (cons ad dd)) n)
                        (exp2 n '() q)
                        (fresh (s) (splito n dd r s)))))
              (conj
                (fresh (a ad add ddd)
                  (disj
                    (conj (== '(1 1) b))
                    (conj (== (cons a (cons ad (cons add ddd))) b))))
                (<lo b n)
                (fresh (bw1 bw nw nw1 ql1 ql s)
                  (conj
                    (exp2 b '() bw1)
                    (pluso bw1 '(1) bw) (<lo q n)
                    (fresh (q1 bwq1)
                      (conj
                        (pluso q '(1) q1)
                        (*o bw q1 bwq1)
                        (<o nw1 bwq1)))
                    (exp2 n '() nw1) (pluso nw1 '(1) nw) (/o nw bw ql1 s)
                    (pluso ql '(1) ql1) (<=lo ql q)
                    (fresh (bql qh s qdh qd)
                      (conj
                        (repeated-mul b ql bql) (/o nw bw1 qh s)
                        (pluso ql qdh qh) (pluso ql qd q) (<=o qd qdh)
                        (fresh (bqd bq1 bq)
                          (conj
                            (repeated-mul b qd bqd)
                            (*o bql bqd bq)
                            (*o b bq bq1)
                            (pluso bq r n)
                            (<o n bq1))))))))))
      (define (exp2 n b q)
        (disj
          (conj (== '(1) n) (== '() q))
          (conj (>1o n) (== '(1) q) (fresh (s) (splito n b s '(1))))
          (conj
            (fresh (q1 b2)
              (conj
                (== (cons 0 q1) q)
                (poso q1)
                (<lo b n)
                (appendo b (cons 1 b) b2)
                (exp2 n b2 q1))))
          (conj
            (fresh (q1 nh b2 s)
              (conj
                (== (cons 1 q1) q)
                (poso q1)
                (poso nh)
                (splito n b s nh)
                (appendo b (cons 1 b) b2)
                (exp2 nh b2 q1))))))
      (define (appendo l s o)
        (disj
          (conj
            (fresh (a d)
              (conj
                (== (cons a d) l)
                (fresh (res)
                  (conj
                    (appendo d s res)
                    (== (cons a res) o))))))
          (conj (== l '()) (== s o))))
      (define (repeated-mul n q nq)
        (disj
          (conj (poso n) (== '() q) (== '(1) nq))
          (conj (== '(1) q) (== n nq))
          (conj
            (>1o q)
            (fresh (q1 nq1)
              (conj
                (pluso q1 '(1) q)
                (repeated-mul n q1 nq1)
                (*o nq1 n nq))))))
      (define (expo b q n) (logo n b q '()))
      (run 10 (t)
        (fresh (n m)
          (conj
            (<=lo n m)
            (*o n '(0 1) m)
            (== (cons n (cons m '())) t))))))
  '((() ())
    ((1) (0 1))
    ((0 1) (0 0 1))
    ((1 1) (0 1 1))
    ((1 _.0 1) (0 1 _.0 1))
    ((0 0 1) (0 0 0 1))
    ((0 1 1) (0 0 1 1))
    ((1 _.0 _.1 1) (0 1 _.0 _.1 1))
    ((0 1 _.0 1) (0 0 1 _.0 1))
    ((0 0 0 1) (0 0 0 0 1))))

(test-check "define expo"
  (value-of
   '(begin
      (define (zeroo n) (== '() n))
      (define (poso n) (fresh (a d) (== (cons a d) n)))
      (define (>1o n) (fresh (a ad dd) (== (cons a (cons ad dd)) n)))
      (define (full-addero b x y r c)
        (disj (conj (== 0 b) (== 0 x) (== 0 y) (== 0 r) (== 0 c))
              (conj (== 1 b) (== 0 x) (== 0 y) (== 1 r) (== 0 c))
              (conj (== 0 b) (== 1 x) (== 0 y) (== 1 r) (== 0 c))
              (conj (== 1 b) (== 1 x) (== 0 y) (== 0 r) (== 1 c))
              (conj (== 0 b) (== 0 x) (== 1 y) (== 1 r) (== 0 c))
              (conj (== 1 b) (== 0 x) (== 1 y) (== 0 r) (== 1 c))
              (conj (== 0 b) (== 1 x) (== 1 y) (== 0 r) (== 1 c))
              (conj (== 1 b) (== 1 x) (== 1 y) (== 1 r) (== 1 c))))
      (define (addero d n m r)
        (disj (conj (== 0 d) (== '() m) (== n r))
              (conj (== 0 d) (== '() n) (== m r) (poso m))
              (conj (== 1 d) (== '() m) (addero 0 n '(1) r))
              (conj (== 1 d) (== '() n) (poso m) (addero 0 '(1) m r))
              (conj (== '(1) n)
                    (== '(1) m)
                    (fresh (a c)
                      (conj
                        (== (cons a (cons c '())) r)
                        (full-addero d 1 1 a c))))
              (conj (== '(1) n) (gen-addero d n m r))
              (conj (== '(1) m) (>1o n) (>1o r) (addero d '(1) n r))
              (conj (>1o n) (gen-addero d n m r))))
      (define (gen-addero d n m r)
        (fresh (a b c e x y z)
          (conj
            (== (cons a x) n)
            (== (cons b y) m)
            (poso y)
            (== (cons c z) r)
            (poso z)
            (full-addero d a b c e)
            (addero e x y z))))
      (define (pluso n m k)
        (addero 0 n m k))
      (define (minuso n m k)
        (pluso m k n))
      (define (*o n m p)
        (disj (conj (== '() n) (== '() p))
              (conj (poso n) (== '() m) (== '() p))
              (conj (== '(1) n) (poso m) (== m p))
              (conj (>1o n) (== '(1) m) (== n p))
              (conj (fresh (x z)
                      (conj
                        (== (cons 0 x) n)
                        (poso x)
                        (== (cons 0 z) p)
                        (poso z)
                        (>1o m)
                        (*o x m z))))
              (conj (fresh (x y)
                      (conj
                        (== (cons 1 x) n)
                        (poso x)
                        (== (cons 0 y) m)
                        (poso y)
                        (*o m n p))))
              (conj (fresh (x y)
                      (conj
                        (== (cons 1 x) n)
                        (poso x)
                        (== (cons 1 y) m)
                        (poso y)
                        (odd-*o x n m p))))))
      (define (odd-*o x n m p)
        (fresh (q)
          (conj
            (bound-*o q p n m)
            (*o x m q)
            (pluso (cons 0 q) m p))))
      (define (bound-*o q p n m)
        (disj
          (conj (== '() q) (poso p))
          (conj
            (fresh (a0 a1 a2 a3 x y z)
              (conj
                (== (cons a0 x) q)
                (== (cons a1 y) p)
                (disj
                  (conj (== '() n) (== (cons a2 z) m) (bound-*o x y z '()))
                  (conj (== (cons a3 z) n) (bound-*o x y z m))))))))
      (define (=lo n m)
        (disj
          (conj (== '() n) (== '() m))
          (conj (== '(1) n) (== '(1) m))
          (conj
            (fresh (a x b y)
              (conj
                (== (cons a x) n)
                (poso x)
                (== (cons b y) m)
                (poso y)
                (=lo x y))))))
      (define (<lo n m)
        (disj
          (conj (== '() n) (poso m))
          (conj (== '(1) n) (>1o m))
          (conj
            (fresh (a x b y)
              (conj
                (== (cons a x) n)
                (poso x)
                (== (cons b y) m)
                (poso y)
                (<lo x y))))))
      (define (<=lo n m) (disj (conj (=lo n m)) (conj (<lo n m))))
      (define (<o n m)
        (disj
          (conj (<lo n m))
          (conj (=lo n m) (fresh (x) (conj (poso x) (pluso n x m))))))
      (define (<=o n m) (disj (conj (== n m)) (conj (<o n m))))
      (define (/o n m q r)
        (disj
          (conj (== r n) (== '() q) (<o n m))
          (conj (== '(1) q) (=lo n m) (pluso r m n) (<o r m))
          (conj
            (<lo m n)
            (<o r m)
            (poso q)
            (fresh (nh nl qh ql qlm qlmr rr rh)
              (conj
                (splito n r nl nh)
                (splito q r ql qh)
                (disj
                  (conj
                    (== '() nh)
                    (== '() qh)
                    (minuso nl r qlm)
                    (*o ql m qlm))
                  (conj
                    (poso nh)
                    (*o ql m qlm)
                    (pluso qlm r qlmr)
                    (minuso qlmr nl rr)
                    (splito rr r '() rh)
                    (/o nh m qh rh))))))))
      (define (splito n r l h)
        (disj (conj (== '() n) (== '() h) (== '() l))
              (conj
                (fresh (b n^)
                  (conj
                    (== (cons 0 (cons b n^)) n)
                    (== '() r)
                    (== (cons b n^) h)
                    (== '() l))))
              (conj
                (fresh (n^)
                  (conj
                    (== (cons 1 n^) n)
                    (== '() r)
                    (== n^ h)
                    (== '(1) l))))
              (conj
                (fresh (b n^ a r^)
                  (conj
                    (== (cons 0 (cons b n^)) n)
                    (== (cons a r^) r)
                    (== '() l)
                    (splito (cons b n^) r^ '() h))))
              (conj
                (fresh (n^ a r^)
                  (conj
                    (== (cons 1 n^) n)
                    (== (cons a r^) r)
                    (== '(1) l)
                    (splito n^ r^ '() h))))
              (conj
                (fresh (b n^ a r^ l^)
                  (conj
                    (== (cons b n^) n)
                    (== (cons a r^) r)
                    (== (cons b l^) l)
                    (poso l^)
                    (splito n^ r^ l^ h))))))
      (define (logo n b q r)
        (disj (conj (== '(1) n) (poso b) (== '() q) (== '() r))
              (conj (== '() q) (<o n b) (pluso r '(1) n))
              (conj (== '(1) q) (>1o b) (=lo n b) (pluso r b n))
              (conj (== '(1) b) (poso q) (pluso r '(1) n))
              (conj (== '() b) (poso q) (== r n))
              (conj (== '(0 1) b)
                    (fresh (a ad dd)
                      (conj
                        (poso dd)
                        (== (cons a (cons ad dd)) n)
                        (exp2 n '() q)
                        (fresh (s) (splito n dd r s)))))
              (conj
                (fresh (a ad add ddd)
                  (disj
                    (conj (== '(1 1) b))
                    (conj (== (cons a (cons ad (cons add ddd))) b))))
                (<lo b n)
                (fresh (bw1 bw nw nw1 ql1 ql s)
                  (conj
                    (exp2 b '() bw1)
                    (pluso bw1 '(1) bw) (<lo q n)
                    (fresh (q1 bwq1)
                      (conj
                        (pluso q '(1) q1)
                        (*o bw q1 bwq1)
                        (<o nw1 bwq1)))
                    (exp2 n '() nw1) (pluso nw1 '(1) nw) (/o nw bw ql1 s)
                    (pluso ql '(1) ql1) (<=lo ql q)
                    (fresh (bql qh s qdh qd)
                      (conj
                        (repeated-mul b ql bql) (/o nw bw1 qh s)
                        (pluso ql qdh qh) (pluso ql qd q) (<=o qd qdh)
                        (fresh (bqd bq1 bq)
                          (conj
                            (repeated-mul b qd bqd)
                            (*o bql bqd bq)
                            (*o b bq bq1)
                            (pluso bq r n)
                            (<o n bq1))))))))))
      (define (exp2 n b q)
        (disj
          (conj (== '(1) n) (== '() q))
          (conj (>1o n) (== '(1) q) (fresh (s) (splito n b s '(1))))
          (conj
            (fresh (q1 b2)
              (conj
                (== (cons 0 q1) q)
                (poso q1)
                (<lo b n)
                (appendo b (cons 1 b) b2)
                (exp2 n b2 q1))))
          (conj
            (fresh (q1 nh b2 s)
              (conj
                (== (cons 1 q1) q)
                (poso q1)
                (poso nh)
                (splito n b s nh)
                (appendo b (cons 1 b) b2)
                (exp2 nh b2 q1))))))
      (define (appendo l s o)
        (disj
          (conj
            (fresh (a d)
              (conj
                (== (cons a d) l)
                (fresh (res)
                  (conj
                    (appendo d s res)
                    (== (cons a res) o))))))
          (conj (== l '()) (== s o))))
      (define (repeated-mul n q nq)
        (disj
          (conj (poso n) (== '() q) (== '(1) nq))
          (conj (== '(1) q) (== n nq))
          (conj
            (>1o q)
            (fresh (q1 nq1)
              (conj
                (pluso q1 '(1) q)
                (repeated-mul n q1 nq1)
                (*o nq1 n nq))))))
      (define (expo b q n) (logo n b q '()))
      (run #f (o) (expo '(1 1) '(1 0 1) o))))
  '((1 1 0 0 1 1 1 1)))
