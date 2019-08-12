;;=============================================================
;; a program built to work with algebra
;;=============================================================
;; 
;; note:
;;  If not specified, assume the algebraic object has finite 
;;  elements
;;
;; 
;; index
;; - scheme stuff
;; - less modern algebra
;; - modern algebra
;; - unit tests
;;
;; 
;; Chicken scheme stuff:
;; ------------------------------------------------------------
;; for older than chicken 5, c-numerals are assumed, so use this
;; (require-library numbers) 
;; The newest specification for scheme, chicken is default r5rs
;; so use this for cleaner r7rs spec
(require-library r7rs) 
;;
;; quality of life improvements
(define true  #t)
(define false #f)
(define (first x) (car x))
(define (rest x) (cdr x))
(define nil '())
(define (mod a b) (modulo a b)) 
;; macro stuff
; special case of two primitives is the intuitive common case
(define-syntax macro
  (syntax-rules ()
    ((macro (id . pattern) template)
     (define-syntax id
       (syntax-rules ()
         ((id . pattern) template))))))

; standard while loop from C and python
(define-syntax while
  (syntax-rules ()
                ((while cond body ...)
                 (let loop ()
                   (when cond
                     body ...
                     (loop))))))

; python style for loop
(define-syntax for
  (syntax-rules (in)
                ((for elem in alist body ...)
                 (for-each (lambda (elem) body ...) alist))))

; starting notion of equality
(define (= a b) (equal? a b)) 
(define (!= a b) (not (= a b)))

(define (index lst ndex)
  "get index of a list, python style"
  (if (or (= 1 (length lst)) 
          (= 0 ndex))
      (car lst)
  (if (= 0 (length lst))
      '()
      (index (cdr lst) 
             (mod (- ndex 1) (length lst))))))

(define (sublist lst start end) 
  "sublist list start end, like list[start:end], python like, currently requires all args"
  (define (cut-front lst start)
    (if (or (= 1 (length lst)) (= 0 start))
        lst
      (if (= 0 (length lst))
          nil
        (cut-front (cdr lst) 
                 (mod (- start 1) (length lst))))))
  (define (cut-back lst end) 
    (define (collect collection index lst)
      (if (= 0 index)
          collection
          (collect (append collection (list (car lst))) 
                   (mod (- index 1) (length lst)) (cdr lst))))
    (collect '() end lst))
  (cut-back (cut-front lst start) end))

;; getters
(define (get-set A) (car A))
(define (get+ A) (cadr A))
(define (get* A) (caddr A))


;;
;;; lesser algebra:
;;    All formalisms that makes the algebra easier such as
;;    first order logic, set theory, category theory, 
;;    type theory, and number theory

;; finite for all quantifier
(define-syntax for-all
  (syntax-rules (in)
                ((for-all elem in alist body)
                 (let ((statement true))
                   (for elem in alist 
                        (if body 
                            'ok 
                            (set! statement false)))
                   statement))))

;; finite exists quantifier
(define-syntax exists
  (syntax-rules (in)
                ((exists elem in alist body)
                 (let ((statement false))
                   (for elem in alist 
                        (if body 
                            (set! statement true)
                            'keep-going))
                   statement))))

;; finite epsilon operator
(define (in? a A)
  (define is-a-in-A? false)
  (for x in A
       (if (= x a) (set! is-a-in-A? true) 'keep-trying))
  is-a-in-A?)

(define (cross A B)
  "cross product commonly seen in naive set theory"
  (define C '())
  (for a in A
       (for b in B
            (set! C (append C (list (list a b))))))
  C)

(define (filter bool-function A)
  "filter : this is the finite axiom schema of specification,
take from set A all elements meeting the specification"
  (define return-list '())
  (for a in A
       (if (bool-function a) 
           (set! return-list (append return-list (list a)))
           'boop))
  return-list)

(define (set= A B)
  "using axiom of extensionality"
  (for-all a in A
       (for-all b in B
            (= a b))))


(define (intersection A B)
  (define C '())
  (for x in A 
       (if (and (and (in? x A) (in? x B)) ; set builder description
                     (not (in? x C)))     ; uniqueness
           (set! C (append C (list x)))
           'do-nothing))
  (for x in B
       (if (and (and (in? x A) (in? x B))
                     (not (in? x C)))     
           (set! C (append C (list x)))
           'do-nothing))
  C)

(define (union A B)
  (define C '())
  (for x in A 
       (if (and (or  (in? x A) (in? x B))
                     (not (in? x C)))     
           (set! C (append C (list x)))
           'do-nothing))
  (for x in B
       (if (and (or  (in? x A) (in? x B))
                     (not (in? x C)))     
           (set! C (append C (list x)))
           'do-nothing))
  C)
  
(define (subset A B)
  (define C '())
  (for x in A 
       (if (and (or (not (in? x A)) (in? x B)) 
                (not (in? x C))) 
           (set! C (append C (list x))) 
           'do-not))
  (for x in B
       (if (and (or (not (in? x A)) (in? x B)) 
                (not (in? x C))) 
           (set! C (append C (list x))) 
           'do-not))
  C)

; difference
; disjoint union


;;
;;; algebra:
;;

(define (get-id A + =)
  (define id 'no-idea)
  (for e in A 
       (if (for-all a in A (= (+ e a) a))
           (set! id e)))
  id)

(define (cross-op A+ B+)
  "set theory cross product but with operators of groups"
  (define (C+ ca cb) 
    (list (A+ (car ca) (car cb))
          (B+ (cadr ca) (cadr cb))))
  C+)

(define (cross-group A B)
  "set theory cross product but with groups"
  (define A-set (get-set A))
  (define A+    (get+    A))
  (define B-set (get-set B))
  (define B+    (get+    B))
  (define C-set (cross A-set B-set))
  (define C+    (cross-op A+ B+))
  (list C-set C+))

(define (cross-ring A B)
  "set theory cross product but with groups"
  (define A-set (get-set A))
  (define A+    (get+    A))
  (define A*    (get*    A))
  (define B-set (get-set B))
  (define B+    (get+    B))
  (define B*    (get*    B))
  (define C-set (cross A-set B-set))
  (define C+    (cross-op A+ B+))
  (define C*    (cross-op A* B*))
  (list C-set C+ C*))

;; primitive parts
(define (closure? A +)
  (for-all a in A
           (for-all b in A
                    (in? (+ a b) A))))

(define (associative? A + =) 
  (for-all a in A
     (for-all b in A
        (for-all c in A
          (= (+ (+ a b) c) (+ a (+ b c)))))))

(define (exists-identity? A + =) 
  (exists e in A 
     (for-all a in A 
        (= (+ a e) a))))

(define (exists-inverse? A + =)
  ; find inverse
  (define id (get-id A + =))
  ; evaluate
  (for-all a in A 
           (exists a-inv in A
                   (= (+ a a-inv) id))))

(define (monoid? A + =)
  "monoid:
        (a + b) + c = a + (b + c), for all a,b,c
        a + 0 = a,                 E. 0, A. a"
  (and (associative? A + =)                
       (exists-identity? A + =)))
                   
(define (group? A + =)
  "group:
        (a + b) + c = a + (b + c), for all a,b,c
        a + 0 = a,                 E. 0, A. a
        a + (-a) = 0,              for all a, there exists -a "
  (and (associative? A + =)                
       (exists-identity? A + =) 
       (exists-inverse? A + =)))

(define (commutative? A + =)
  (for-all a in A
       (for-all b in A
            (= (+ a b) (+ b a)))))
                
(define (abelian-group? A + =)
  (and (group? A + =)
       (commutative? A + =)))

(define (right-distributive? A + * =)
  (for-all a in A
     (for-all b in A
        (for-all c in A
           (= (* a (+ b c)) (+ (* a b) (* a c)))))))

(define (left-distributive? A + * =)
  (for-all a in A
     (for-all b in A
        (for-all c in A
           (= (* (+ b c) a) (+ (* b a) (* c a)))))))
         
(define (ring? A + * =)
  " ring:
    albelian group:
        a + b = b + a,             for all a,b
        (a + b) + c = a + (b + c), for all a,b,c
        a + 0 = a,                 there exists a 0, for all a
        a + (-a) = 0               for all a, there exists -a
    a(bc) = (ab)c,    for all a,b,c
    a(b+c) = ab + ac, for all a,b,c
    (b+c)a = ba + ca, for all a,b,c"
  (and  (abelian-group? A + =)
        (associative? A * =)
        (right-distributive? A + * =)
        (left-distributive? A + * =)))

(define (abelian-ring? A + * =)
  (and (ring? A + * =) 
       (commutative? A * =)))

(define (ring-with-id? A + * =)
  (and (ring? A + * =)
       (exists-identity? A * =)
       (not (= (get-id A + =) 
               (get-id A * =)))))

(define (integral-domain? A + * =)
  (define id+ (get-id A + =))
  (and (ring-with-id? A + * =) 
       (abelian-ring? A + * =)
       ; for all a,b in A, if ab != 0, then a=0 or b=0
       (for-all a in A
          (for-all b in A
             (or (not (= (* a b) id+)) 
                 (= a id+) 
                 (= b id+))))))

(define (division-ring? A + * =)
  (define id+ (get-id A + =))
  (define id* (get-id A * =))
  (define A* (filter (lambda (a) (not (= a id+))) A)) ; A without 0
  (and (integral-domain? A + * =)
        (for-all a in A*
           (exists a-inv in A* 
                   (and (= (* a a-inv) id*) 
                        (= (* a-inv a) id*))))))

(define (field? A + * =)
  (define id+ (get-id A + =))
  (define A* (filter (lambda (a) (not (= a id+))) A)) ; A without 0
  (and (abelian-group? A + =)
       (abelian-group? A* * =)
       (right-distributive? A + * =)))

(define (subring? S + * =)
  " A nonempty subset S of a ring R is a subring if S is closed under
subtraction and multiplication. That is, if a - b and ab are in S
whenever a and b are in S "
  (for-all a in S
           (for-all b in S
                    (and (in? (+ a (inverse b)) S) (in? (* a b) S)))))

(define (cayley-table A +)
  (define CT '())
  (for a in A
       (define temp '())
       (for b in A
            (set! temp (append temp (list (+ a b)))))
       (set! CT (append CT (list temp))))
  CT)

(define (print-cayley-table! A +)
  (newline)
  (define CT '())
  (for a in A
       (define temp '())
       (for b in A
            (set! temp (append temp (list (+ a b)))))
       (display temp) (newline)))

;; object generators
(define (Z_n n)
  "Z_n ring : integers mod n, both + and * ops included"
  (define i 0)
  (define A '())
  (while (< i n)
         (set! A (append A (list i)))
         (set! i (+ 1 i)))
  (list A 
        (lambda (a b) (mod (+ a b) n))
        (lambda (a b) (mod (* a b) n))))


(define (matrix-multiply matrix1 matrix2)
  (map
   (lambda (row)
    (apply map
     (lambda column
      (apply + (map * row column)))
     matrix2))
   matrix1))
(matrix-multiply '((1 2) (3 4)) '((-3 -8 3) (-2 1 4))) ; ((-7 -6 11) (-17 -20 25))

;;
;;; unit tests:
;;
(define z5 (Z_n 5))
z5
(define A  (get-set z5))
(define A+ (get+    z5))
(define A* (get*    z5))

(define z6 (Z_n 6))
(define B  (get-set z6))
(define B+ (get+    z6))
(define B* (get*    z6))

(define z3 (Z_n 3))
(define C  (cross    z3 z3))
(define C+ (cross-op z3 z3))


(print-cayley-table! A A+) 
(print-cayley-table! A A*) 
(print-cayley-table! B B+) 
(print-cayley-table! B B*)

;C
;(print-cayley-table! C C+)



;(define (group-isomorphism? A A+ B B+)
;  (list (= (length A) (length B)) 

; other bunch of types of rings
; isomorphisms on these
; cosets, sylov stuff
; unity in a ring is a nonzero element that is an identity for multiplication

; these really need better semantics



(for-all a in A (exists b in B (= b a)))
(in? 1 A)
(filter (lambda (a) (not (= a 1))) A)
(group? A A+ =)
(abelian-group? A A+ =)
(integral-domain? A A+ A* =)
(ring? A A+ A* =)
(abelian-ring? A A+ A* =)
(ring-with-id? A A+ A* =)
(division-ring? A A+ A* =)
(field? A A+ A* =)
(intersection A B)
(union A B)
(subset A B)
