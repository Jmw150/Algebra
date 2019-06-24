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
;; - first order logic
;; - algebra
;; - unit test
;;
;; 
;; Chicken scheme stuff:
;; ------------------------------------------------------------
;; for older than chicken 5, c-numerals are assumed, so use this
;; (require-library numbers) 
;; The newest specification for scheme, chicken is default r5rs
(require-library r7rs) 
;;
;; quality of life stuff
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

; while loop
(define-syntax while
  (syntax-rules ()
    ((_ condition . body)
     (let loop () (cond (condition (begin . body) (loop)))))))

; python style for loop
(define-syntax for
  (syntax-rules (in)
                ((for elem in alist body ...)
                 (for-each (lambda (elem) body ...) alist))))

; standard while loop from C and python
(define-syntax while
  (syntax-rules ()
                ((while cond body ...)
                 (let loop ()
                   (when cond
                     body ...
                     (loop))))))

(define (= a b) (equal? a b)) ; this can be set to mean other things
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
;;; first order logic:
;;
(define-syntax for-all
  (syntax-rules (in)
                ((for-all elem in alist body)
                 (let ((statement true))
                   (for elem in alist 
                        (if body 
                            'ok 
                            (set! statement false)))
                   statement))))

(define-syntax exists
  (syntax-rules (in)
                ((exists elem in alist body)
                 (let ((statement false))
                   (for elem in alist 
                        (if body 
                            (set! statement true)
                            'keep-going))
                   statement))))
;(for-all a in A (exists b in B (= b a)))

(define (in? a A)
  (define is-a-in-A? false)
  (for x in A
       (if (= x a) (set! is-a-in-A? true) 'keep-trying))
  is-a-in-A?)
;(in? 1 A)

;;
;;; algebra:
;;

(define (get-id A + =)
  (define id 'no-idea)
  (for e in A 
       (if (for-all a in A (= (+ e a) a))
           (set! id e)))
  id)

(define (X A B)
  "set theory cross product but with groups"
  (define A-set (get-set A))
  (define A+    (get+    A))
  (define B-set (get-set B))
  (define B+    (get+    B))
  (define C '())
  (for a in A-set
       (for b in B-set
            (set! C (append C (list (list a b))))))
  (define (C+ ca cb) 
    (list (A+ (car ca) (car cb))
          (B+ (cadr ca) (cadr cb))))
  (list C C+))



(define (filter bool-function A)
  (define return-list '())
  (for a in A
       (if (bool-function a) 
           (set! return-list (append return-list (list a)))
           'boop))
  return-list)
;(filter (lambda (a) (not (= a 1))) A)

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
;(group? A A+ =)

(define (commutative? A + =)
  (for-all a in A
       (for-all b in A
            (= (+ a b) (+ b a)))))
                
(define (abelian-group? A + =)
  (and (group? A + =)
       (commutative? A + =)))
;(abelian-group? A A-op =)

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
;(ring? A A+ A* =)

(define (abelian-ring? A + * =)
  (and (ring? A + * =) 
       (commutative? A * =)))
;(abelian-ring? A A+ A* =)

(define (ring-with-id? A + * =)
  (and (ring? A + * =)
       (exists-identity? A * =)
       (not (= (get-id A + =) 
               (get-id A * =)))))
;(ring-with-id? A A+ A* =)

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
;(integral-domain? A A+ A* =)

(define (division-ring? A + * =)
  (define id+ (get-id A + =))
  (define id* (get-id A * =))
  (define A* (filter (lambda (a) (not (= a id+))) A)) ; A without 0
  (and (integral-domain? A + * =)
        (for-all a in A*
           (exists a-inv in A* 
                   (and (= (* a a-inv) id*) 
                        (= (* a-inv a) id*))))))
;(division-ring? A A+ A* =)

(define (field? A + * =)
  (define id+ (get-id A + =))
  (define A* (filter (lambda (a) (not (= a id+))) A)) ; A without 0
  (and (abelian-group? A + =)
       (abelian-group? A* * =)
       (right-distributive? A + * =)))
;(field? A A+ A* =)

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



;; unit test:
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
(define C  (get-set (X z3 z3)))
(define C+ (get+ (X z3 z3)))


;(print-cayley-table! A A+) 
;(print-cayley-table! A A*) 
;(print-cayley-table! B B+) 
;(print-cayley-table! B B*)

;C
;(print-cayley-table! C C+)



;(define (group-isomorphism? A A+ B B+)
;  (list (= (length A) (length B)) 

; other bunch of types of rings
; isomorphisms on these
; cosets, sylov stuff
; unity in a ring is a nonzero element that is an identity for multiplication

; these really need better semantics

;(define (intersection A B)
;  (define C '())
;  (for a in A
;       (for b in B
;            (if (and (and (in? a A) (in? b B)) ; classical def
;                     (not (in? a C)))          ; cut redundancy
;                (set! C (append C (list a)))
;                'do-not)))
;  C)
;(intersection A B)
;
;(define (union A B)
;  (define C '())
;  (for a in A
;       (for b in B
;            (if (and (or (in? a A) (in? b B)) ; classical def
;                     (not (in? b C)))         ; cut redundancy
;                (set! C (append C (list b))) 
;                'do-not)))
;  C)
;(union A B)
;  
;(define (subset A B)
;  (define C '())
;  (for a in A
;       (for b in B
;            (if (and (or (not (in? a A)) (in? b B))
;                     (not (in? a C)))         ; cut redundancy
;                (set! C (append C (list a))) 
;                'do-not)))
;  C)
;(subset A B)
;"
;

