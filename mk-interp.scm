;;; miniKanren interpreter (with a subset of Scheme as well)
;;;
;;; Written in the style of Indiana University's C311/B521 courses
;;; by Jason Hemann, Dan Friedman, and Will Byrd

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
  (lambda (env x flag) 
    (pmatch env
      (() (errorf 'apply-env "not in env ~s" x))  
      (((env ,y* . ,a*) ,env^) (guard (memq x y*))
       (apply-rib y* a* x))
      (((rec-env ,y* . ,a*) ,env^) (guard (memq x y*))
       (let ((lam-exp (apply-rib y* a* x)))
         (eval-exp lam-exp env flag)))
      (else (apply-env (cadr env) x flag)))))

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
  (lambda (exp)
    (eval-exp exp '() #f)))

(define eval-exp
  (lambda (exp env flag)
    (pmatch exp
      (,b (guard (boolean? b)) b)
      (,x (guard (symbol? x)) (apply-env env x flag))
      (,n (guard (number? n)) n)
      ((list . ,e*) (eval-exp* e* env flag))
      ((lambda ,x* ,body) (guard (for-all symbol? x*))
       (lambda (a*)
         (let ((env (ext-env* x* a* env)))
            (eval-exp body env flag))))
      ((quote ,val) val)
      ((zero? ,e) (zero? (eval-exp e env flag)))
      ((sub1 ,e) (sub1 (eval-exp e env flag)))
      ((* ,ne ,me) (* (eval-exp ne env flag) (eval-exp me env flag)))
      ((cons ,e1 ,e2) (cons (eval-exp e1 env flag) (eval-exp e2 env flag)))
      ((if ,te ,ce ,ae)
       (if (eval-exp te env flag) (eval-exp ce env flag) (eval-exp ae env flag)))
      ((letrec ,def* ,body)
       (let ((env^ (ext-rec-env* (map car def*) (map cadr def*) env)))
         (eval-exp body env^ flag)))
      ((let ,def* ,body)
       (let ((var* (map car def*))
             (val* (map (lambda (x) (eval-exp (cadr x) env flag)) def*)))
         (eval-exp body (ext-env* var* val* env) flag)))
      ((run ,nexp (,x) . ,ge*) 
       (if flag (error 'eval-exp "Cannot re-enter run")
         (let ((n (eval-exp nexp env #t))
               (x-var (var x)))
           (let ((env^ (ext-env* `(,x) `(,x-var) env)))
             (let ((g (conj (eval-exp* ge* env^ #t))))
               (let ((a* (take n (lambdaf@ () (g '())))))
                 (map (reify x-var) a*)))))))
      ((== ,u ,v)
       (if (not flag) (error 'eval-exp "Not in run(*)")
         (lambda (s)
           (lambdaf@ ()
             (let ((u (eval-exp u env flag))
                   (v (eval-exp v env flag)))
               (cond
                 ((unify u v s) => unit)
                 (else (mzero))))))))
      ((fresh ,x* . ,ge*) (guard (for-all symbol? x*))
       (if (not flag) (error 'eval-exp "Not in run(*)")
         (let ((env^ (ext-env* x* (map var x*) env)))
           (lambda (s)
             ((conj (eval-exp* ge* env^ flag)) s)))))
      ((conde . ,ge*s)
       (if (not flag) (error 'eval-exp "Not in run(*)")
         (lambda (s)
           ((disj (map (lambda (ge*) (eval-exp* ge* env flag)) ge*s)) s))))
      ((,rator . ,rand*) ((eval-exp rator env flag) (eval-exp* rand* env flag)))
      (else (error 'eval-exp "Invalid rator" rator)))))

(define eval-exp*
  (lambda (exp* env flag)
    (map (lambda (e) (eval-exp e env flag)) exp*)))

(define disj
  (lambda (g*s)
    (lambda (s)
      (lambdaf@ ()
        (cond
          ((null? g*s) (mzero))
          (else
           (mplus ((conj (car g*s)) s)
             (lambdaf@ () ((disj (cdr g*s)) s)))))))))

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
;;; Helpers for miniKanren.

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

;; (test-check "non-composed run"
;;   (value-of  '(run 1 (x) (== (run 1 (q) (== 5 q)) '(5))))
;;   "Exception in eval-exp: Cannot re-enter run
;;     Type (debug) to enter the debugger."

(test-check "non-overlapping run"
  (value-of  '(cons (run 1 (x) (== x 4)) (run 1 (x) (== x 5))))
  '((4) . (5)))

(test-check "gets 5"
  (value-of '5)
5)

(test-check "gets 5"
  (value-of '((lambda (x) x) 5))
  5)

;;; Changing numexp and nummval to go away.

(test-check "basic works"
  (value-of '(((lambda (x) (lambda (y) x)) 5) 6))
  '5)

(test-check "overridable special forms"
  (value-of '((lambda (quote) quote) 5))
  '5)

(test-check "variadic lambdas"
  (value-of '((lambda (a b c)
                (cons a (cons b (cons c '()))))
              4
              0
              2))
  '(4 0 2))

(test-check "list"
  (value-of '(list 1 3 4))
  '(1 3 4))

(test-check "letrec e? o?"
  (value-of ' (let ((t #t)
                    (f #f))
                (letrec ((e? (lambda (n)
                               (if (zero? n)
                                   t
                                   (o? (sub1 n)))))
                         (o? (lambda (n)
                               (if (zero? n)
                                   f
                                   (e? (sub1 n))))))
                  (o? 15))))
  #t)

(test-check "letrec e? o? b"
  (value-of ' (let ((t #t)
                    (f #f))
                (letrec ((e? (lambda (n)
                               (if (zero? n)
                                   t
                                   (o? (sub1 n)))))
                         (o? (lambda (n)
                               (if (zero? n)
                                   f
                                   (e? (sub1 n))))))
                  (o? 14))))
  #f)

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
                 (== q q)
                 (== 5 5))))
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
                 (== b 7)                       
                 (== q (cons a (cons b '())))
                 (== a 5))))
  '((5 7)))

(test-check "fresh-3b"
  (value-of '(run 1 (q)
               (fresh (a b)                  
                 (== a 5)
                 (== b 7)
                 (== q (cons a (cons b '()))))))
  '((5 7)))

(test-check "fresh-3c"
  (value-of '(run 1 (q)
               (fresh (a b)                  
                 (== q (cons a (cons b '())))
                 (== b 7) (== a 5))))
  '((5 7)))

(test-check "fresh n*0"
  (value-of '(run 1 (q)
               (fresh (a b c)                  
                 (== q (cons a (cons b (cons c '()))))                  
                 (== b 7)
                 (== c 7)
                 (== a 5))))
  '((5 7 7)))

(test-check "fresh n*1"
  (value-of '(run 1 (q)
               (fresh (a b c)                  
                 (== q (cons a (cons b (cons c '()))))                  
                 (== b 7)
                 (== c 6)
                 (== a 5))))
  '((5 7 6)))

(test-check "fresh n*2"
  (value-of '(run 1 (q)
               (fresh (a b c)                  
                 (== b 7)
                 (== q (cons a (cons b (cons c '()))))
                 (== c 6)
                 (== a 5))))
  '((5 7 6)))

(test-check "fresh n*3"
  (value-of '(run 1 (q)
               (fresh (a b c)
                 (== b 7)
                 (== c 6)                  
                 (== q (cons a (cons b (cons c '()))))
                 (== a 5))))
  '((5 7 6)))

(test-check "fresh n*4"
  (value-of '(run 1 (q)
               (fresh (a b c)                  
                 (== b 7)                          
                 (== c 6)
                 (== a 5)                                
                 (== q (cons a (cons b (cons c '())))))))
  '((5 7 6)))

(test-check "fresh works"
  (value-of '(run 1 (x)
               (fresh (y z)
                 (== x (cons y (cons z '()))))))
  '((_.0 _.1)))

(test-check "fresh worksb"
  (value-of '(run 1 (x)
               (fresh (y z)
                 (== y 5)
                 (== z y)
                 (== x (cons y (cons z '()))))))
  '((5 5)))

(test-check "same goals in a fresh"
  (value-of '(run 4 (q)
               (fresh (a b)
                 (== a 4)                        
                 (== b 6)
                 (== a 4)                        
                 (== b 6)
                 (== (cons a (cons b '())) q))))
  '((4 6)))

(test-check "distinct vars"
  (value-of
   '(run #f (q)
      (fresh (j) 
        (== q j)
        (== #f #f))))
  '(_.0))

(test-check "failure of both branches"
  (value-of '(run 1 (q)
               (fresh (j)
                 (== q q) (== 5 6))))
  '())

(test-check "run-g 1"
  (value-of '(run 1 (x)
               (conde
                 [(== x 5)]
                 [(== x 6)])))
  '(5))

(test-check "run-g 2"
  (value-of '(run 2 (x)
               (conde
                 [(== x 5)]
                 [(== x 6)])))
  '(5 6))

(test-check "run*"
  (value-of '(run #f (x)
               (conde
                 [(== x 5)]                 
                 [(== x 6)])))
  '(5 6))

;; (test-check "conde-true"
;;   (value-of '(run 1 (q) (conde [])))
;;   '(_.0))

(test-check "conde-false"
  (value-of '(run 1 (q) (conde)))
  '())

(test-check "conde 3"
  (value-of '(run 4 (q)
               (conde
                 ((== q 3))                 
                 ((conde
                    ((== q 6))                    
                    ((== q 4)))))))
  '(3 6 4))

(test-check "third"
  (value-of '(run 2 (q)
               (conde
                 [(== 5 q)]
                 [(== 6 q)])))
  '(5 6))

(test-check "run* 2 ans"
  (value-of '(run #f (q)
               (conde
                 [(== 5 q)]
                 [(== 6 q)])))
  '(5 6))

(test-check "four"
  (value-of '(run 3 (q)
               (conde
                 [(== q 5)]
                 [(conde
                    [(== q 6)]
                    [(== q 7)])])))
  '(5 6 7))

(test-check "five"
  (value-of '(run #f (q)
               (conde
                 ((== q 5))
                 ((conde
                    ((== q 6))
                    ((== q 7)))))))
  '(5 6 7))

(test-check "failure of one branch"
  (value-of '(run #f (q)
               (fresh (j)
                 (conde ((== q j))
                        ((== 3 4)))
                 (== #f #f))))
  '(_.0))

(test-check "success of both branches"
  (value-of '(run #f (q)
               (fresh (j)                  
                 (conde ((== q j))
                        ((== q j)))
                 (== #f #f))))
  '(_.0 _.0))

(test-check "ground success of both branches"
  (value-of '(run #f (q)
               (conde
                 ((== q 3))
                 ((== q 6)))))
  '(3 6))

(test-check "breaking conde"
  (value-of '(run #f (q)
               (fresh (a b)                  
                 (conde
                   ((conde
                      ((== a 6))
                      ((== a 5)))
                    (== a q))
                   ((== q 4))))))
  '(4 5 6))

(test-check "conde/fresh working"
  (value-of '(run 4 (q)
               (fresh (a b)                  
                 (conde
                   ((== a 4))
                   ((conde
                      ((== a 5))
                      ((== a 6)))))
                 (== b 7)
                 (== (cons a (cons b '())) q))))
  '((4 7)
    (6 7)
    (5 7)))

(test-check "multiple runs through conde"
  (value-of '(run 4 (q)
               (fresh (a b)                  
                 (== (cons a (cons b '())) q)
                 (conde
                   ((== a 4))                         
                   ((conde
                      ((== a 3))                            
                      ((== a 5)))))                          
                 (== b 4))))
  '((4 4)
    (5 4)
    (3 4)))

(test-check "nested conde, basic"
  (value-of '(run 4 (q)
               (fresh (a b)                  
                 (conde
                   ((== a 3))                        
                   ((== a 4)))                       
                 (== a q))))
  '(3 4))

(test-check "nested conde"
  (value-of '(run 4 (q)
               (fresh (a b)                  
                 (conde
                   ((== a 3))                         
                   ((== a 4)))                        
                 (== b 7)                                              
                 (== (cons a (cons b '())) q))))
  '((3 7)
    (4 7)))

(test-check "12 answers"
  (value-of '(run #f (q)
               (fresh (a b)
                 (conde
                   [(== b 0)
                    (conde
                      [(== a 0)]
                      [(== a 1)]
                      [(== a 2)]
                      [(== a 3)])]
                   [(== b 1)
                    (conde
                      [(== a 0)]
                      [(== a 1)]
                      [(== a 2)]
                      [(== a 3)])]
                   [(== b 2)
                    (conde
                      [(== a 0)]
                      [(== a 1)]
                      [(== a 2)]
                      [(== a 3)])])
                 (== (cons a (cons b '())) q))))
  '((0 0) (1 0) (2 0) (0 1) (3 0) (0 2) (1 1) (1 2) (2 1) (3 1) (3 2) (2 2)))

(test-check "proper-listo"
  (value-of '(run 7 (q)
               (let ([f (lambda (f)
                          (lambda (q)
                            (conde
                              ((== q '()))                              
                              ((fresh (a d)                                
                                 (== (cons a d) q)
                                 ((f f) d))))))])
                 ((f f) q))))
  '(()
    (_.0)
    (_.0 _.1)
    (_.0 _.1 _.2)
    (_.0 _.1 _.2 _.3)
    (_.0 _.1 _.2 _.3 _.4)
    (_.0 _.1 _.2 _.3 _.4 _.5)))


(test-check "curried appendo"
  (value-of '(run 10 (q)
               (fresh (a b c)
                 (== (cons a (cons b (cons c '()))) q)
                 (let ([f (lambda (f)
                            (lambda (x)
                              (lambda (y)
                                (lambda (z)
                                  (conde
                                    ((== '() x)
                                     (== y z))                                        
                                    ((fresh (h i j)
                                       (== (cons h i) x)
                                       (== (cons h j) z)
                                       ((((f f) i) y) j))))))))])
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

(test-check "letrec proper listo"
  (value-of '(run 7 (q)
               (letrec ((proper-listo
                         (lambda (l)
                           (conde
                             ((== l '()))                                   
                             ((fresh (a d)                                     
                                (== (cons a d) l)
                                (proper-listo d)))))))
                 (proper-listo q))))
  '(()
    (_.0)
    (_.0 _.1)
    (_.0 _.1 _.2)
    (_.0 _.1 _.2 _.3)
    (_.0 _.1 _.2 _.3 _.4)
    (_.0 _.1 _.2 _.3 _.4 _.5)))

(test-check "uncurried appendo"
  (value-of '(run 4 (q)
               (letrec ([appendo (lambda (l s o)
                                   (conde
                                     ((fresh (a d)                                          
                                        (== (cons a d) l)
                                        (fresh (res)
                                          (appendo d s res)
                                          (== (cons a res) o))))
                                     ((== l '()) (== s o))))])
                 (fresh (a b c)                    
                   (appendo a b c)                            
                   (== (cons a (cons b (cons c '()))) q)))))
  '((() _.0 _.0)
    ((_.0) _.1 (_.0 . _.1))
    ((_.0 _.1) _.2 (_.0 _.1 . _.2))
    ((_.0 _.1 _.2) _.3 (_.0 _.1 _.2 . _.3))))

(test-check "uncurried appendo the normal way"
  (value-of '(run 4 (q)
               (letrec ([appendo (lambda (l s o)
                                   (conde
                                     ((== l '()) (== s o))
                                     ((fresh (a d)                                          
                                        (== (cons a d) l)
                                        (fresh (res)
                                          (appendo d s res)
                                          (== (cons a res) o))))))])
                 (fresh (a b c)                    
                   (appendo a b c)                            
                   (== (cons a (cons b (cons c '()))) q)))))
  '((() _.0 _.0)
    ((_.0) _.1 (_.0 . _.1))
    ((_.0 _.1) _.2 (_.0 _.1 . _.2))
    ((_.0 _.1 _.2) _.3 (_.0 _.1 _.2 . _.3))))

(define build-num
  (lambda (n)
    (cond
      ((odd? n)
       (cons 1 (build-num (quotient (- n 1) 2))))
      ((and (not (zero? n)) (even? n))
       (cons 0
         (build-num (quotient n 2))))
      ((zero? n) '()))))

(test-check "booleano 1"
  (value-of
   '(letrec
        ((zeroo (lambda (n) (== '() n)))
         (poso (lambda (n) (fresh (a d) (== (cons a d) n))))
         (>1o (lambda (n) (fresh (a ad dd) (== (cons a (cons ad dd)) n))))
         (full-addero
          (lambda (b x y r c)
            (conde ((== 0 b) (== 0 x) (== 0 y) (== 0 r) (== 0 c))
                   ((== 1 b) (== 0 x) (== 0 y) (== 1 r) (== 0 c))
                   ((== 0 b) (== 1 x) (== 0 y) (== 1 r) (== 0 c))
                   ((== 1 b) (== 1 x) (== 0 y) (== 0 r) (== 1 c))
                   ((== 0 b) (== 0 x) (== 1 y) (== 1 r) (== 0 c))
                   ((== 1 b) (== 0 x) (== 1 y) (== 0 r) (== 1 c))
                   ((== 0 b) (== 1 x) (== 1 y) (== 0 r) (== 1 c))
                   ((== 1 b) (== 1 x) (== 1 y) (== 1 r) (== 1 c)))))
         (addero
          (lambda (d n m r)
            (conde ((== 0 d) (== '() m) (== n r))
                   ((== 0 d) (== '() n) (== m r) (poso m))
                   ((== 1 d) (== '() m) (addero 0 n '(1) r))
                   ((== 1 d) (== '() n) (poso m) (addero 0 '(1) m r))
                   ((== '(1) n)
                    (== '(1) m)
                    (fresh (a c) (== (list a c) r) (full-addero d 1 1 a c)))
                   ((== '(1) n) (gen-addero d n m r))
                   ((== '(1) m) (>1o n) (>1o r) (addero d '(1) n r))
                   ((>1o n) (gen-addero d n m r)))))
         (gen-addero
          (lambda (d n m r)
            (fresh (a b c e x y z) (== (cons a x) n) (== (cons b y) m)
                   (poso y) (== (cons c z) r) (poso z) (full-addero d a b c e)
                   (addero e x y z))))
         (pluso (lambda (n m k) (addero 0 n m k)))
         (minuso (lambda (n m k) (pluso m k n)))
         (*o (lambda (n m p)
               (conde ((== '() n) (== '() p)) ((poso n) (== '() m) (== '() p))
                      ((== '(1) n) (poso m) (== m p))
                      ((>1o n) (== '(1) m) (== n p))
                      ((fresh (x z) (== (cons 0 x) n) (poso x) (== (cons 0 z) p)
                              (poso z) (>1o m) (*o x m z)))
                      ((fresh (x y) (== (cons 1 x) n) (poso x) (== (cons 0 y) m)
                              (poso y) (*o m n p)))
                      ((fresh (x y) (== (cons 1 x) n) (poso x) (== (cons 1 y) m)
                              (poso y) (odd-*o x n m p))))))
         (odd-*o
          (lambda (x n m p)
            (fresh
                (q)
              (bound-*o q p n m)
              (*o x m q)
              (pluso (cons 0 q) m p))))
         (bound-*o
          (lambda (q p n m)
            (conde
              ((== '() q) (poso p))
              ((fresh
                   (a0 a1 a2 a3 x y z)
                 (== (cons a0 x) q)
                 (== (cons a1 y) p)
                 (conde
                   ((== '() n) (== (cons a2 z) m) (bound-*o x y z '()))
                   ((== (cons a3 z) n) (bound-*o x y z m))))))))
         (=lo (lambda (n m)
                (conde
                  ((== '() n) (== '() m))
                  ((== '(1) n) (== '(1) m))
                  ((fresh (a x b y) (== (cons a x) n) (poso x)
                          (== (cons b y) m) (poso y) (=lo x y))))))
         (<lo (lambda (n m)
                (conde
                  ((== '() n) (poso m))
                  ((== '(1) n) (>1o m))
                  ((fresh (a x b y) (== (cons a x) n) (poso x)
                          (== (cons b y) m) (poso y) (<lo x y))))))
         (<=lo (lambda (n m) (conde ((=lo n m)) ((<lo n m)))))
         (<o (lambda (n m)
               (conde
                 ((<lo n m))
                 ((=lo n m) (fresh (x) (poso x) (pluso n x m))))))
         (<=o (lambda (n m) (conde ((== n m)) ((<o n m)))))
         (/o (lambda (n m q r)
               (conde
                 ((== r n) (== '() q) (<o n m))
                 ((== '(1) q) (=lo n m) (pluso r m n) (<o r m))
                 ((<lo m n)
                  (<o r m)
                  (poso q)
                  (fresh
                      (nh nl qh ql qlm qlmr rr rh)
                    (splito n r nl nh)
                    (splito q r ql qh)
                    (conde
                      ((== '() nh) (== '() qh) (minuso nl r qlm) (*o ql m qlm))
                      ((poso nh) (*o ql m qlm) (pluso qlm r qlmr)
                       (minuso qlmr nl rr) (splito rr r '() rh)
                       (/o nh m qh rh))))))))
         (splito
          (lambda (n r l h)
            (conde ((== '() n) (== '() h) (== '() l))
                   ((fresh (b n^) (== (cons 0 (cons b n^)) n) (== '() r)
                           (== (cons b n^) h) (== '() l)))
                   ((fresh (n^) (== (cons 1 n^) n) (== '() r) (== n^ h)
                           (== '(1) l)))
                   ((fresh (b n^ a r^) (== (cons 0 (cons b n^)) n) (== (cons a r^) r)
                           (== '() l) (splito (cons b n^) r^ '() h)))
                   ((fresh (n^ a r^) (== (cons 1 n^) n) (== (cons a r^) r)
                           (== '(1) l) (splito n^ r^ '() h)))
                   ((fresh (b n^ a r^ l^) (== (cons b n^) n) (== (cons a r^) r)
                           (== (cons b l^) l) (poso l^) (splito n^ r^ l^ h))))))
         (logo
          (lambda (n b q r)
            (conde ((== '(1) n) (poso b) (== '() q) (== '() r))
                   ((== '() q) (<o n b) (pluso r '(1) n))
                   ((== '(1) q) (>1o b) (=lo n b) (pluso r b n))
                   ((== '(1) b) (poso q) (pluso r '(1) n))
                   ((== '() b) (poso q) (== r n))
                   ((== '(0 1) b)
                    (fresh (a ad dd) (poso dd) (== (cons a (cons ad dd)) n)
                           (exp2 n '() q) (fresh (s) (splito n dd r s))))
                   ((fresh
                        (a ad add ddd)
                      (conde ((== '(1 1) b)) ((== (cons a (cons ad (cons add ddd))) b))))
                    (<lo b n)
                    (fresh (bw1 bw nw nw1 ql1 ql s) (exp2 b '() bw1)
                           (pluso bw1 '(1) bw) (<lo q n)
                           (fresh
                               (q1 bwq1)
                             (pluso q '(1) q1)
                             (*o bw q1 bwq1)
                             (<o nw1 bwq1))
                           (exp2 n '() nw1) (pluso nw1 '(1) nw) (/o nw bw ql1 s)
                           (pluso ql '(1) ql1) (<=lo ql q)
                           (fresh (bql qh s qdh qd) (repeated-mul b ql bql) (/o nw bw1 qh s)
                                  (pluso ql qdh qh) (pluso ql qd q) (<=o qd qdh)
                                  (fresh (bqd bq1 bq) (repeated-mul b qd bqd) (*o bql bqd bq)
                                         (*o b bq bq1) (pluso bq r n) (<o n bq1))))))))
         (exp2
          (lambda (n b q)
            (conde
              ((== '(1) n) (== '() q))
              ((>1o n) (== '(1) q) (fresh (s) (splito n b s '(1))))
              ((fresh (q1 b2) (== (cons 0 q1) q) (poso q1) (<lo b n)
                      (appendo b (cons 1 b) b2) (exp2 n b2 q1)))
              ((fresh (q1 nh b2 s) (== (cons 1 q1) q) (poso q1) (poso nh)
                      (splito n b s nh) (appendo b (cons 1 b) b2)
                      (exp2 nh b2 q1))))))
         (appendo
          (lambda (l s o)
            (conde
              ((fresh
                   (a d)
                 (== (cons a d) l)
                 (fresh (res) (appendo d s res) (== (cons a res) o))))
              ((== l '()) (== s o)))))
         (repeated-mul
          (lambda (n q nq)
            (conde
              ((poso n) (== '() q) (== '(1) nq))
              ((== '(1) q) (== n nq))
              ((>1o q)
               (fresh
                   (q1 nq1)
                 (pluso q1 '(1) q)
                 (repeated-mul n q1 nq1)
                 (*o nq1 n nq))))))
         (expo (lambda (b q n) (logo n b q '()))))
      (run 10 (t)
        (fresh (n m)
          (<=lo n m)
          (*o n '(0 1) m)
          (== (list n m) t)))))
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

(test-check "heretofore broken test works with booleans"
  (value-of
   '(letrec
        ((zeroo (lambda (n) (== '() n)))
         (poso (lambda (n) (fresh (a d) (== (cons a d) n))))
         (>1o (lambda (n) (fresh (a ad dd) (== (cons a (cons ad dd)) n))))
         (full-addero
          (lambda (b x y r c)
            (conde ((== 0 b) (== 0 x) (== 0 y) (== 0 r) (== 0 c))
                   ((== 1 b) (== 0 x) (== 0 y) (== 1 r) (== 0 c))
                   ((== 0 b) (== 1 x) (== 0 y) (== 1 r) (== 0 c))
                   ((== 1 b) (== 1 x) (== 0 y) (== 0 r) (== 1 c))
                   ((== 0 b) (== 0 x) (== 1 y) (== 1 r) (== 0 c))
                   ((== 1 b) (== 0 x) (== 1 y) (== 0 r) (== 1 c))
                   ((== 0 b) (== 1 x) (== 1 y) (== 0 r) (== 1 c))
                   ((== 1 b) (== 1 x) (== 1 y) (== 1 r) (== 1 c)))))
         (addero
          (lambda (d n m r)
            (conde ((== 0 d) (== '() m) (== n r))
                   ((== 0 d) (== '() n) (== m r) (poso m))
                   ((== 1 d) (== '() m) (addero 0 n '(1) r))
                   ((== 1 d) (== '() n) (poso m) (addero 0 '(1) m r))
                   ((== '(1) n)
                    (== '(1) m)
                    (fresh (a c) (== (list a c) r) (full-addero d 1 1 a c)))
                   ((== '(1) n) (gen-addero d n m r))
                   ((== '(1) m) (>1o n) (>1o r) (addero d '(1) n r))
                   ((>1o n) (gen-addero d n m r)))))
         (gen-addero
          (lambda (d n m r)
            (fresh (a b c e x y z) (== (cons a x) n) (== (cons b y) m)
                   (poso y) (== (cons c z) r) (poso z) (full-addero d a b c e)
                   (addero e x y z))))
         (pluso (lambda (n m k) (addero 0 n m k)))
         (minuso (lambda (n m k) (pluso m k n)))
         (*o (lambda (n m p)
               (conde ((== '() n) (== '() p)) ((poso n) (== '() m) (== '() p))
                      ((== '(1) n) (poso m) (== m p))
                      ((>1o n) (== '(1) m) (== n p))
                      ((fresh (x z) (== (cons 0 x) n) (poso x) (== (cons 0 z) p)
                              (poso z) (>1o m) (*o x m z)))
                      ((fresh (x y) (== (cons 1 x) n) (poso x) (== (cons 0 y) m)
                              (poso y) (*o m n p)))
                      ((fresh (x y) (== (cons 1 x) n) (poso x) (== (cons 1 y) m)
                              (poso y) (odd-*o x n m p))))))
         (odd-*o
          (lambda (x n m p)
            (fresh
                (q)
              (bound-*o q p n m)
              (*o x m q)
              (pluso (cons 0 q) m p))))
         (bound-*o
          (lambda (q p n m)
            (conde
              ((== '() q) (poso p))
              ((fresh
                   (a0 a1 a2 a3 x y z)
                 (== (cons a0 x) q)
                 (== (cons a1 y) p)
                 (conde
                   ((== '() n) (== (cons a2 z) m) (bound-*o x y z '()))
                   ((== (cons a3 z) n) (bound-*o x y z m))))))))
         (=lo (lambda (n m)
                (conde
                  ((== '() n) (== '() m))
                  ((== '(1) n) (== '(1) m))
                  ((fresh (a x b y) (== (cons a x) n) (poso x)
                          (== (cons b y) m) (poso y) (=lo x y))))))
         (<lo (lambda (n m)
                (conde
                  ((== '() n) (poso m))
                  ((== '(1) n) (>1o m))
                  ((fresh (a x b y) (== (cons a x) n) (poso x)
                          (== (cons b y) m) (poso y) (<lo x y))))))
         (<=lo (lambda (n m) (conde ((=lo n m)) ((<lo n m)))))
         (<o (lambda (n m)
               (conde
                 ((<lo n m))
                 ((=lo n m) (fresh (x) (poso x) (pluso n x m))))))
         (<=o (lambda (n m) (conde ((== n m)) ((<o n m)))))
         (/o (lambda (n m q r)
               (conde
                 ((== r n) (== '() q) (<o n m))
                 ((== '(1) q) (=lo n m) (pluso r m n) (<o r m))
                 ((<lo m n)
                  (<o r m)
                  (poso q)
                  (fresh
                      (nh nl qh ql qlm qlmr rr rh)
                    (splito n r nl nh)
                    (splito q r ql qh)
                    (conde
                      ((== '() nh) (== '() qh) (minuso nl r qlm) (*o ql m qlm))
                      ((poso nh) (*o ql m qlm) (pluso qlm r qlmr)
                       (minuso qlmr nl rr) (splito rr r '() rh)
                       (/o nh m qh rh))))))))
         (splito
          (lambda (n r l h)
            (conde ((== '() n) (== '() h) (== '() l))
                   ((fresh (b n^) (== (cons 0 (cons b n^)) n) (== '() r)
                           (== (cons b n^) h) (== '() l)))
                   ((fresh (n^) (== (cons 1 n^) n) (== '() r) (== n^ h)
                           (== '(1) l)))
                   ((fresh (b n^ a r^) (== (cons 0 (cons b n^)) n) (== (cons a r^) r)
                           (== '() l) (splito (cons b n^) r^ '() h)))
                   ((fresh (n^ a r^) (== (cons 1 n^) n) (== (cons a r^) r)
                           (== '(1) l) (splito n^ r^ '() h)))
                   ((fresh (b n^ a r^ l^) (== (cons b n^) n) (== (cons a r^) r)
                           (== (cons b l^) l) (poso l^) (splito n^ r^ l^ h))))))
         (logo
          (lambda (n b q r)
            (conde ((== '(1) n) (poso b) (== '() q) (== '() r))
                   ((== '() q) (<o n b) (pluso r '(1) n))
                   ((== '(1) q) (>1o b) (=lo n b) (pluso r b n))
                   ((== '(1) b) (poso q) (pluso r '(1) n))
                   ((== '() b) (poso q) (== r n))
                   ((== '(0 1) b)
                    (fresh (a ad dd) (poso dd) (== (cons a (cons ad dd)) n)
                           (exp2 n '() q) (fresh (s) (splito n dd r s))))
                   ((fresh
                        (a ad add ddd)
                      (conde ((== '(1 1) b)) ((== (cons a (cons ad (cons add ddd))) b))))
                    (<lo b n)
                    (fresh (bw1 bw nw nw1 ql1 ql s) (exp2 b '() bw1)
                           (pluso bw1 '(1) bw) (<lo q n)
                           (fresh
                               (q1 bwq1)
                             (pluso q '(1) q1)
                             (*o bw q1 bwq1)
                             (<o nw1 bwq1))
                           (exp2 n '() nw1) (pluso nw1 '(1) nw) (/o nw bw ql1 s)
                           (pluso ql '(1) ql1) (<=lo ql q)
                           (fresh (bql qh s qdh qd) (repeated-mul b ql bql) (/o nw bw1 qh s)
                                  (pluso ql qdh qh) (pluso ql qd q) (<=o qd qdh)
                                  (fresh (bqd bq1 bq) (repeated-mul b qd bqd) (*o bql bqd bq)
                                         (*o b bq bq1) (pluso bq r n) (<o n bq1))))))))
         (exp2
          (lambda (n b q)
            (conde
              ((== '(1) n) (== '() q))
              ((>1o n) (== '(1) q) (fresh (s) (splito n b s '(1))))
              ((fresh (q1 b2) (== (cons 0 q1) q) (poso q1) (<lo b n)
                      (appendo b (cons 1 b) b2) (exp2 n b2 q1)))
              ((fresh (q1 nh b2 s) (== (cons 1 q1) q) (poso q1) (poso nh)
                      (splito n b s nh) (appendo b (cons 1 b) b2)
                      (exp2 nh b2 q1))))))
         (appendo
          (lambda (l s o)
            (conde
              ((fresh
                   (a d)
                 (== (cons a d) l)
                 (fresh (res) (appendo d s res) (== (cons a res) o))))
              ((== l '()) (== s o)))))
         (repeated-mul
          (lambda (n q nq)
            (conde
              ((poso n) (== '() q) (== '(1) nq))
              ((== '(1) q) (== n nq))
              ((>1o q)
               (fresh
                   (q1 nq1)
                 (pluso q1 '(1) q)
                 (repeated-mul n q1 nq1)
                 (*o nq1 n nq))))))
         (expo (lambda (b q n) (logo n b q '()))))
      (run 10 (t)
        (fresh (n m)
          (<=lo n m)
          (*o n '(0 1) m)
          (== (list n m) t)))))
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

(test-check "heretofore broken test works with booleano"
  (value-of
   '(letrec
        ((zeroo (lambda (n) (== '() n)))
         (poso (lambda (n) (fresh (a d) (== (cons a d) n))))
         (>1o (lambda (n) (fresh (a ad dd) (== (cons a (cons ad dd)) n))))
         (full-addero
          (lambda (b x y r c)
            (conde ((== 0 b) (== 0 x) (== 0 y) (== 0 r) (== 0 c))
                   ((== 1 b) (== 0 x) (== 0 y) (== 1 r) (== 0 c))
                   ((== 0 b) (== 1 x) (== 0 y) (== 1 r) (== 0 c))
                   ((== 1 b) (== 1 x) (== 0 y) (== 0 r) (== 1 c))
                   ((== 0 b) (== 0 x) (== 1 y) (== 1 r) (== 0 c))
                   ((== 1 b) (== 0 x) (== 1 y) (== 0 r) (== 1 c))
                   ((== 0 b) (== 1 x) (== 1 y) (== 0 r) (== 1 c))
                   ((== 1 b) (== 1 x) (== 1 y) (== 1 r) (== 1 c)))))
         (addero
          (lambda (d n m r)
            (conde ((== 0 d) (== '() m) (== n r))
                   ((== 0 d) (== '() n) (== m r) (poso m))
                   ((== 1 d) (== '() m) (addero 0 n '(1) r))
                   ((== 1 d) (== '() n) (poso m) (addero 0 '(1) m r))
                   ((== '(1) n)
                    (== '(1) m)
                    (fresh (a c) (== (list a c) r) (full-addero d 1 1 a c)))
                   ((== '(1) n) (gen-addero d n m r))
                   ((== '(1) m) (>1o n) (>1o r) (addero d '(1) n r))
                   ((>1o n) (gen-addero d n m r)))))
         (gen-addero
          (lambda (d n m r)
            (fresh (a b c e x y z) (== (cons a x) n) (== (cons b y) m)
                   (poso y) (== (cons c z) r) (poso z) (full-addero d a b c e)
                   (addero e x y z))))
         (pluso (lambda (n m k) (addero 0 n m k)))
         (minuso (lambda (n m k) (pluso m k n)))
         (*o (lambda (n m p)
               (conde ((== '() n) (== '() p)) ((poso n) (== '() m) (== '() p))
                      ((== '(1) n) (poso m) (== m p))
                      ((>1o n) (== '(1) m) (== n p))
                      ((fresh (x z) (== (cons 0 x) n) (poso x) (== (cons 0 z) p)
                              (poso z) (>1o m) (*o x m z)))
                      ((fresh (x y) (== (cons 1 x) n) (poso x) (== (cons 0 y) m)
                              (poso y) (*o m n p)))
                      ((fresh (x y) (== (cons 1 x) n) (poso x) (== (cons 1 y) m)
                              (poso y) (odd-*o x n m p))))))
         (odd-*o
          (lambda (x n m p)
            (fresh
                (q)
              (bound-*o q p n m)
              (*o x m q)
              (pluso (cons 0 q) m p))))
         (bound-*o
          (lambda (q p n m)
            (conde
              ((== '() q) (poso p))
              ((fresh
                   (a0 a1 a2 a3 x y z)
                 (== (cons a0 x) q)
                 (== (cons a1 y) p)
                 (conde
                   ((== '() n) (== (cons a2 z) m) (bound-*o x y z '()))
                   ((== (cons a3 z) n) (bound-*o x y z m))))))))
         (=lo (lambda (n m)
                (conde
                  ((== '() n) (== '() m))
                  ((== '(1) n) (== '(1) m))
                  ((fresh (a x b y) (== (cons a x) n) (poso x)
                          (== (cons b y) m) (poso y) (=lo x y))))))
         (<lo (lambda (n m)
                (conde
                  ((== '() n) (poso m))
                  ((== '(1) n) (>1o m))
                  ((fresh (a x b y) (== (cons a x) n) (poso x)
                          (== (cons b y) m) (poso y) (<lo x y))))))
         (<=lo (lambda (n m) (conde ((=lo n m)) ((<lo n m)))))
         (<o (lambda (n m)
               (conde
                 ((<lo n m))
                 ((=lo n m) (fresh (x) (poso x) (pluso n x m))))))
         (<=o (lambda (n m) (conde ((== n m)) ((<o n m)))))
         (/o (lambda (n m q r)
               (conde
                 ((== r n) (== '() q) (<o n m))
                 ((== '(1) q) (=lo n m) (pluso r m n) (<o r m))
                 ((<lo m n)
                  (<o r m)
                  (poso q)
                  (fresh
                      (nh nl qh ql qlm qlmr rr rh)
                    (splito n r nl nh)
                    (splito q r ql qh)
                    (conde
                      ((== '() nh) (== '() qh) (minuso nl r qlm) (*o ql m qlm))
                      ((poso nh) (*o ql m qlm) (pluso qlm r qlmr)
                       (minuso qlmr nl rr) (splito rr r '() rh)
                       (/o nh m qh rh))))))))
         (splito
          (lambda (n r l h)
            (conde ((== '() n) (== '() h) (== '() l))
                   ((fresh (b n^) (== (cons 0 (cons b n^)) n) (== '() r)
                           (== (cons b n^) h) (== '() l)))
                   ((fresh (n^) (== (cons 1 n^) n) (== '() r) (== n^ h)
                           (== '(1) l)))
                   ((fresh (b n^ a r^) (== (cons 0 (cons b n^)) n) (== (cons a r^) r)
                           (== '() l) (splito (cons b n^) r^ '() h)))
                   ((fresh (n^ a r^) (== (cons 1 n^) n) (== (cons a r^) r)
                           (== '(1) l) (splito n^ r^ '() h)))
                   ((fresh (b n^ a r^ l^) (== (cons b n^) n) (== (cons a r^) r)
                           (== (cons b l^) l) (poso l^) (splito n^ r^ l^ h))))))
         (logo
          (lambda (n b q r)
            (conde ((== '(1) n) (poso b) (== '() q) (== '() r))
                   ((== '() q) (<o n b) (pluso r '(1) n))
                   ((== '(1) q) (>1o b) (=lo n b) (pluso r b n))
                   ((== '(1) b) (poso q) (pluso r '(1) n))
                   ((== '() b) (poso q) (== r n))
                   ((== '(0 1) b)
                    (fresh (a ad dd) (poso dd) (== (cons a (cons ad dd)) n)
                           (exp2 n '() q) (fresh (s) (splito n dd r s))))
                   ((fresh
                        (a ad add ddd)
                      (conde ((== '(1 1) b)) ((== (cons a (cons ad (cons add ddd))) b))))
                    (<lo b n)
                    (fresh (bw1 bw nw nw1 ql1 ql s) (exp2 b '() bw1)
                           (pluso bw1 '(1) bw) (<lo q n)
                           (fresh
                               (q1 bwq1)
                             (pluso q '(1) q1)
                             (*o bw q1 bwq1)
                             (<o nw1 bwq1))
                           (exp2 n '() nw1) (pluso nw1 '(1) nw) (/o nw bw ql1 s)
                           (pluso ql '(1) ql1) (<=lo ql q)
                           (fresh (bql qh s qdh qd) (repeated-mul b ql bql) (/o nw bw1 qh s)
                                  (pluso ql qdh qh) (pluso ql qd q) (<=o qd qdh)
                                  (fresh (bqd bq1 bq) (repeated-mul b qd bqd) (*o bql bqd bq)
                                         (*o b bq bq1) (pluso bq r n) (<o n bq1))))))))
         (exp2
          (lambda (n b q)
            (conde
              ((== '(1) n) (== '() q))
              ((>1o n) (== '(1) q) (fresh (s) (splito n b s '(1))))
              ((fresh (q1 b2) (== (cons 0 q1) q) (poso q1) (<lo b n)
                      (appendo b (cons 1 b) b2) (exp2 n b2 q1)))
              ((fresh (q1 nh b2 s) (== (cons 1 q1) q) (poso q1) (poso nh)
                      (splito n b s nh) (appendo b (cons 1 b) b2)
                      (exp2 nh b2 q1))))))
         (appendo
          (lambda (l s o)
            (conde
              ((fresh
                   (a d)
                 (== (cons a d) l)
                 (fresh (res) (appendo d s res) (== (cons a res) o))))
              ((== l '()) (== s o)))))
         (repeated-mul
          (lambda (n q nq)
            (conde
              ((poso n) (== '() q) (== '(1) nq))
              ((== '(1) q) (== n nq))
              ((>1o q)
               (fresh
                   (q1 nq1)
                 (pluso q1 '(1) q)
                 (repeated-mul n q1 nq1)
                 (*o nq1 n nq))))))
         (expo (lambda (b q n) (logo n b q '()))))
      (run 10 (t)
        (fresh (n m)
          (<=lo n m)
          (*o n '(0 1) m)
          (== (list n m) t)))))
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

;;; The next test too long to run.

(test-check "exp test with booleans"
  (value-of
   '(letrec
        ((zeroo (lambda (n) (== '() n)))
         (poso (lambda (n) (fresh (a d) (== (cons a d) n))))
         (>1o (lambda (n) (fresh (a ad dd) (== (cons a (cons ad dd)) n))))
         (full-addero
          (lambda (b x y r c)
            (conde ((== 0 b) (== 0 x) (== 0 y) (== 0 r) (== 0 c))
                   ((== 1 b) (== 0 x) (== 0 y) (== 1 r) (== 0 c))
                   ((== 0 b) (== 1 x) (== 0 y) (== 1 r) (== 0 c))
                   ((== 1 b) (== 1 x) (== 0 y) (== 0 r) (== 1 c))
                   ((== 0 b) (== 0 x) (== 1 y) (== 1 r) (== 0 c))
                   ((== 1 b) (== 0 x) (== 1 y) (== 0 r) (== 1 c))
                   ((== 0 b) (== 1 x) (== 1 y) (== 0 r) (== 1 c))
                   ((== 1 b) (== 1 x) (== 1 y) (== 1 r) (== 1 c)))))
         (addero
          (lambda (d n m r)
            (conde ((== 0 d) (== '() m) (== n r))
                   ((== 0 d) (== '() n) (== m r) (poso m))
                   ((== 1 d) (== '() m) (addero 0 n '(1) r))
                   ((== 1 d) (== '() n) (poso m) (addero 0 '(1) m r))
                   ((== '(1) n)
                    (== '(1) m)
                    (fresh (a c) (== (list a c) r) (full-addero d 1 1 a c)))
                   ((== '(1) n) (gen-addero d n m r))
                   ((== '(1) m) (>1o n) (>1o r) (addero d '(1) n r))
                   ((>1o n) (gen-addero d n m r)))))
         (gen-addero
          (lambda (d n m r)
            (fresh (a b c e x y z) (== (cons a x) n) (== (cons b y) m)
                   (poso y) (== (cons c z) r) (poso z) (full-addero d a b c e)
                   (addero e x y z))))
         (pluso (lambda (n m k) (addero 0 n m k)))
         (minuso (lambda (n m k) (pluso m k n)))
         (*o (lambda (n m p)
               (conde ((== '() n) (== '() p)) ((poso n) (== '() m) (== '() p))
                      ((== '(1) n) (poso m) (== m p))
                      ((>1o n) (== '(1) m) (== n p))
                      ((fresh (x z) (== (cons 0 x) n) (poso x) (== (cons 0 z) p)
                              (poso z) (>1o m) (*o x m z)))
                      ((fresh (x y) (== (cons 1 x) n) (poso x) (== (cons 0 y) m)
                              (poso y) (*o m n p)))
                      ((fresh (x y) (== (cons 1 x) n) (poso x) (== (cons 1 y) m)
                              (poso y) (odd-*o x n m p))))))
         (odd-*o
          (lambda (x n m p)
            (fresh
                (q)
              (bound-*o q p n m)
              (*o x m q)
              (pluso (cons 0 q) m p))))
         (bound-*o
          (lambda (q p n m)
            (conde
              ((== '() q) (poso p))
              ((fresh
                   (a0 a1 a2 a3 x y z)
                 (== (cons a0 x) q)
                 (== (cons a1 y) p)
                 (conde
                   ((== '() n) (== (cons a2 z) m) (bound-*o x y z '()))
                   ((== (cons a3 z) n) (bound-*o x y z m))))))))
         (=lo (lambda (n m)
                (conde
                  ((== '() n) (== '() m))
                  ((== '(1) n) (== '(1) m))
                  ((fresh (a x b y) (== (cons a x) n) (poso x)
                          (== (cons b y) m) (poso y) (=lo x y))))))
         (<lo (lambda (n m)
                (conde
                  ((== '() n) (poso m))
                  ((== '(1) n) (>1o m))
                  ((fresh (a x b y) (== (cons a x) n) (poso x)
                          (== (cons b y) m) (poso y) (<lo x y))))))
         (<=lo (lambda (n m) (conde ((=lo n m)) ((<lo n m)))))
         (<o (lambda (n m)
               (conde
                 ((<lo n m))
                 ((=lo n m) (fresh (x) (poso x) (pluso n x m))))))
         (<=o (lambda (n m) (conde ((== n m)) ((<o n m)))))
         (/o (lambda (n m q r)
               (conde
                 ((== r n) (== '() q) (<o n m))
                 ((== '(1) q) (=lo n m) (pluso r m n) (<o r m))
                 ((<lo m n)
                  (<o r m)
                  (poso q)
                  (fresh
                      (nh nl qh ql qlm qlmr rr rh)
                    (splito n r nl nh)
                    (splito q r ql qh)
                    (conde
                      ((== '() nh) (== '() qh) (minuso nl r qlm) (*o ql m qlm))
                      ((poso nh) (*o ql m qlm) (pluso qlm r qlmr)
                       (minuso qlmr nl rr) (splito rr r '() rh)
                       (/o nh m qh rh))))))))
         (splito
          (lambda (n r l h)
            (conde ((== '() n) (== '() h) (== '() l))
                   ((fresh (b n^) (== (cons 0 (cons b n^)) n) (== '() r)
                           (== (cons b n^) h) (== '() l)))
                   ((fresh (n^) (== (cons 1 n^) n) (== '() r) (== n^ h)
                           (== '(1) l)))
                   ((fresh (b n^ a r^) (== (cons 0 (cons b n^)) n) (== (cons a r^) r)
                           (== '() l) (splito (cons b n^) r^ '() h)))
                   ((fresh (n^ a r^) (== (cons 1 n^) n) (== (cons a r^) r)
                           (== '(1) l) (splito n^ r^ '() h)))
                   ((fresh (b n^ a r^ l^) (== (cons b n^) n) (== (cons a r^) r)
                           (== (cons b l^) l) (poso l^) (splito n^ r^ l^ h))))))
         (logo
          (lambda (n b q r)
            (conde ((== '(1) n) (poso b) (== '() q) (== '() r))
                   ((== '() q) (<o n b) (pluso r '(1) n))
                   ((== '(1) q) (>1o b) (=lo n b) (pluso r b n))
                   ((== '(1) b) (poso q) (pluso r '(1) n))
                   ((== '() b) (poso q) (== r n))
                   ((== '(0 1) b)
                    (fresh (a ad dd) (poso dd) (== (cons a (cons ad dd)) n)
                           (exp2 n '() q) (fresh (s) (splito n dd r s))))
                   ((fresh
                        (a ad add ddd)
                      (conde ((== '(1 1) b)) ((== (cons a (cons ad (cons add ddd))) b))))
                    (<lo b n)
                    (fresh (bw1 bw nw nw1 ql1 ql s) (exp2 b '() bw1)
                           (pluso bw1 '(1) bw) (<lo q n)
                           (fresh
                               (q1 bwq1)
                             (pluso q '(1) q1)
                             (*o bw q1 bwq1)
                             (<o nw1 bwq1))
                           (exp2 n '() nw1) (pluso nw1 '(1) nw) (/o nw bw ql1 s)
                           (pluso ql '(1) ql1) (<=lo ql q)
                           (fresh (bql qh s qdh qd) (repeated-mul b ql bql) (/o nw bw1 qh s)
                                  (pluso ql qdh qh) (pluso ql qd q) (<=o qd qdh)
                                  (fresh (bqd bq1 bq) (repeated-mul b qd bqd) (*o bql bqd bq)
                                         (*o b bq bq1) (pluso bq r n) (<o n bq1))))))))
         (exp2
          (lambda (n b q)
            (conde
              ((== '(1) n) (== '() q))
              ((>1o n) (== '(1) q) (fresh (s) (splito n b s '(1))))
              ((fresh (q1 b2) (== (cons 0 q1) q) (poso q1) (<lo b n)
                      (appendo b (cons 1 b) b2) (exp2 n b2 q1)))
              ((fresh (q1 nh b2 s) (== (cons 1 q1) q) (poso q1) (poso nh)
                      (splito n b s nh) (appendo b (cons 1 b) b2)
                      (exp2 nh b2 q1))))))
         (appendo
          (lambda (l s o)
            (conde
              ((fresh
                   (a d)
                 (== (cons a d) l)
                 (fresh (res) (appendo d s res) (== (cons a res) o))))
              ((== l '()) (== s o)))))
         (repeated-mul
          (lambda (n q nq)
            (conde
              ((poso n) (== '() q) (== '(1) nq))
              ((== '(1) q) (== n nq))
              ((>1o q)
               (fresh (q1 nq1)
                 (pluso q1 '(1) q)
                 (repeated-mul n q1 nq1)
                 (*o nq1 n nq))))))
         (expo (lambda (b q n) (logo n b q '()))))
      (run #f (o) (expo '(1 1) '(1 0 1) o))))
  '((1 1 0 0 1 1 1 1)))

