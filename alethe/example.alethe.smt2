; AN UNSAT DERIVATION USING CUTTING PLANES PROOF SYSTEM
; OVER BITVECTOR OPERATIONS, i.e. no such 'y' exists.

(set-logic QF_BV)
(declare-fun x () (_ BitVec 2))
(declare-fun y () (_ BitVec 2))

(assert (= x #b01))
(assert (= (bvand x y) #b10))

;; pb-blasting process of (bvand x y), with r being the name of AND(x,y)

(step i1
  (cl (= x (pbbT (! (_ intOf x 0) :named @x0) (! (_ intOf x 1) :named @x1)))
    :rule pbblast_pbvar))

(step i2
  (cl (= y (pbbT (! (_ intOf y 0) :named @y0) (! (_ intOf y 1) :named @y1)))
    :rule pbblast_pbvar))

(step i3
  (cl (= (! (bvand x y) :named @r) (bvand (pbbT @x0 @x1) (pbbT @y0 @y1))))
    :rule cong :premises (i1 i2))

(step i4
  (cl
    (and
      (=
        (bvand (pbbT @x0 @x1) (pbbT @y0 @y1))
        (pbbT (! (_ intOf @r 0) :named @r0) (! (_ intOf @r 1) :named @r1))
        )
      (>= (- @x0 @r0) 0)
      (>= (- @x1 @r1) 0)
      (>= (- @y0 @r0) 0)
      (>= (- @y1 @r1) 0)
      (>= (- @r0 @x0 @y0) (- 1))
      (>= (- @r1 @x1 @y1) (- 1))
    ))  :rule pbblast_step_bvand)

(step i5
  (cl
    (=
        (bvand (pbbT @x0 @x1) (pbbT @y0 @y1))
        (pbbT (! (_ intOf @r 0) :named @r0) (! (_ intOf @r 1) :named @r1))
    ))  :rule and :premises i4 :args 1)

(step i6
  (cl (=
        (bvand x y)
        (pbbT @r0 @r1)
  )) :rule trans :premises (i3 i5))

(step i7
  (cl (=
        #b10
        (pbbT 0 1)
  )) :rule pbblast_pbbconst :args #b10)

(step i8
  (cl (=
        (= (bvand x y) #b10)
        (= (pbbT @r0 @r1) (pbbT 0 1))
  )) :rule cong :premises i6 i7)

(step i9
  (cl (=
        (= (pbbT @r0 @r1) (pbbT 0 1))
        (= (- (+ @r1 (* 2 @r0)) (+ 1 (* 2 0))) 0)
  )) :rule pbblast_bveq :args (pbbT @r0 @r1) (pbbT 0 1))

(step i10
  (cl (=
        (= (bvand x y) #b10)
        (= (- (+ @r1 (* 2 @r0)) (+ 1 (* 2 0))) 0)
  )) :rule trans :premises i8 i9)
































;; pb-blasting process of (bvand x y), with r being the name of AND(x,y)
(step i0
  (cl (= x (pbbT (! (_ intOf x 0) :named @x0) (! (_ intOf x 1) :named @x1)))
    :rule pb_blast_step_var))
(step i1
  (cl (= y (pbbT (! (_ intOf y 0) :named @y0) (! (_ intOf y 1) :named @y1)))
    :rule pb_blast_step_var))

(step i2
  (cl (= (! (bvand x y) :named @r) (bvand (pbbT @x0 @x1) (pbbT @y0 @y1))
        ))
  :rule cong :premises (i0 i1))

(step i3
  (cl
    (and
      (=
        (bvand (pbbT @x0 @x1) (pbbT @y0 @y1))
        (pbbT (! (_ intOf @r 0) :named @r0) (! (_ intOf @r 1) :named @r1))
        )
      (>= (- @x0 @r0) 0)
      (>= (- @x1 @r1) 0)
      (>= (- @y0 @r0) 0)
      (>= (- @y1 @r1) 0)
      (>= (- @r0 @x0 @y0) (- 1))
      (>= (- @r1 @x1 @y1) (- 1))
    )  :rule pbblast_step_bvand))

;; Confirm this:
(step i4
  (cl
    (and
      (=
        (pbbT (! (_ intOf @r 0) :named @r0) (! (_ intOf @r 1) :named @r1))
        (= (- (+ (* 1 @r1) (* 2 @r0) 0)
              (+ (* 1 1) (* 2 0) 0))
          0))
      (>= (- @x0 @r0) 0)
      (>= (- @x1 @r1) 0)
      (>= (- @y0 @r0) 0)
      (>= (- @y1 @r1) 0)
      (>= (- @r0 @x0 @y0) (- 1))
      (>= (- @r1 @x1 @y1) (- 1))
    )  :rule pbblast_step_bveq))


;; bit-blasting process of the above:

;;   (step i0 (cl (= x (bbT (_ bitOf x 0) (_ bitOf x 1))) :rule bv_bitblast_step_var)
;;   (step i1 (cl (= y (bbT (_ bitOf y 0) (_ bitOf y 1))) :rule bv_bitblast_step_var)

;; (step i2
;;  (cl
;;    (=
;;      (bvand x y)
;;      (bvand (bbT (_ bitOf x 0) (_ bitOf x 1)) (bbT (_ bitOf y 0) (_ bitOf y 1))))) :rule cong :premises (i0 i1))

;; (step i3
;;  (cl
;;    (=
;;      (bvand (bbT (_ bitOf x 0) (_ bitOf x 1)) (bbT (_ bitOf y 0) (_ bitOf y 1)))
;;      (bbT (and (_ bitOf x 0) (_ bitOf y 0)) (and (_ bitOf x 1) (_ bitOf y 1))))) :rule bv_bitblast_step_bvand)

;; (step i4 (cl (= #b10 (bbT false true)) :rule bv_bitblast_step_const))

;; (step i5
;;   (cl
;;     (= (bbT (and (_ bitOf x 0) (_ bitOf y 0)) (and (_ bitOf x 1) (_ bitOf y 1))) (bbT false true))
;;     (and (= (and (_ bitOf x 0) (_ bitOf y 0)) false) (= (and (_ bitOf x 1) (_ bitOf y 1)) true)) :rule bv_bitblast_step_bveq))

;; (step i_n
;;  (cl
;;    (=
;;      (= (bvand x y) #b10)
;;      (and (= (and (_ bitOf x 0) (_ bitOf y 0)) false) (= (and (_ bitOf x 1) (_ bitOf y 1)) true)))) :rule ...))

; EQUAL RULE
; (+ (2^i*(bvand(x,y))) - (+ (2^i * z)) = 0

; BLASTING
; x0 := (_ bitOf x 0)
; x1 := (_ bitOf x 1)
; y0 := (_ bitOf y 0)
; y1 := (_ bitOf y 1)
; r0 := (and (_ bitOf x 0) (_ bitOf y 0))
; r1 := (and (_ bitOf x 1) (_ bitOf y 1))

; AND RULE

; r_i: bits of (bvand x y)
; z_i: bits of #b10

; 2r0 + r1 -2z0 -z1 = 0,
; x0 - r0 >= 0,
; x1 - r1 >= 0,
; y0 - r0 >= 0,
; y1 - r1 >= 0,
; r0 - x0 - y0 >= -1,
; r1 - x1 - y1 >= -1

; Normalized Constraints (x + !x = 1)
; c1 :  2r0 + r1 + 2!z0 + !z1 >= 3,
(define-fun c1 () Bool (>= (+ (* 2 (and (_ bitOf x 0) (_ bitOf y 0))) (* 1 (and (_ bitOf x 1) (_ bitOf y 1))) (* 2 (- 1 (_ bigOf z 0))) (* 1 (- 1 (_ bitOf z 1))) 0) 3))
; c2 :  2!r0 + !r1 + 2z0 + z1 >= 3,
(define-fun c2 () Bool (>= (+ (* 2 (- 1 (and (_ bitOf x 0) (_ bitOf y 0)))) (* 1 (- 1 (and (_ bitOf x 1) (_ bitOf y 1)))) (* 2 (_ bigOf z 0)) (* 1 (_ bitOf z 1)) 0) 3))
; c3 :  x0 + !r0 >= 1,
(define-fun c3 () Bool (>= (+ (* 1 (_ bitOf x 0)) (* 1 (- 1 (and (_ bitOf x 0) (_ bitOf y 0)))) 0) 1))
; c4 :  x1 + !r1 >= 1,
(define-fun c4 () Bool (>= (+ (* 1 (_ bitOf x 1)) (* 1 (- 1 (and (_ bitOf x 1) (_ bitOf y 1)))) 0) 1))
; c5 :  y0 + !r0 >= 1,
(define-fun c5 () Bool (>= (+ (* 1 (_ bitOf y 0)) (* 1 (- 1 (and (_ bitOf x 0) (_ bitOf y 0)))) 0) 1))
; c6 :  y1 + !r1 >= 1,
(define-fun c6 () Bool (>= (+ (* 1 (_ bitOf y 1)) (* 1 (- 1 (and (_ bitOf x 1) (_ bitOf y 1)))) 0) 1))
; c7 :  r0 + !x0 + !y0 >= 1,
(define-fun c7 () Bool (>= (+ (* 1 (and (_ bitOf x 0) (_ bitOf y 0))) (* 1 (- 1 (_ bitOf x 0))) (* 1 (- 1 (_ bitOf y 0))) 0) 1))
; c8 :  r1 + !x1 + !y1 >= 1,
(define-fun c8 () Bool (>= (+ (* 1 (and (_ bitOf x 1) (_ bitOf y 1))) (* 1 (- 1 (_ bitOf x 1))) (* 1 (- 1 (_ bitOf y 1))) 0) 1))
; c9 :  !x0 >= 1,
(define-fun c9 () Bool (>= (+ (* 1 (- 1 (_ bitOf x 0))) 0) 1))
; c10 : x1 >= 1,
(define-fun c10 () Bool (>= (+ (* 1 (_ bitOf x 1)) 0) 1))
; c11 : z0 >= 1,
(define-fun c11 () Bool (>= (+ (* 1 (_ bigOf z 0)) 0) 1))
; c12 : !z1 >= 1
(define-fun c12 () Bool (>= (+ (* 1 (- 1 (_ bitOf z 1))) 0) 1))


; Cutting Planes Reasoning
; c13 : !r0 >= 1 : cp_addition c3 c9
(step c13 (cl
            (>=
              (+ (* 1 (- 1 (and (_ bitOf x 0) (_ bitOf y 0)))) 0)
              1)) :rule cp_addition :premises (c3 c9))
; c14 : 2!r0 >= 2 : cp_multiplication c13 2
(step c14 (cl (>= (+ (* 2 (- 1 (and (_ bitOf x 0) (_ bitOf y 0)))) 0) 2)) :rule cp_multiplication :premises (c13) :args (2))
; c15 : r1 + 2!z0 + !z1 >= 3 : cp_addition c1 c14
(step c15 (cl (>= (+ (* 1 (and (_ bitOf x 1) (_ bitOf y 1))) (* 2 (- 1 (_ bigOf z 0))) (* 1 (- 1 (_ bitOf z 1))) 0) 3)) :rule cp_addition :premises (c1 c14))
; c16 : 2z0 >= 2 : cp_multiplication c11 2
(step c16 (cl (>= (+ (* 2 (_ bigOf z 0)) 0) 2)) :rule cp_multiplication :premises (c11) :args (2))
; c17 : r1 + !z1 >= 3 : cp_addition c15 c16
(step c17 (cl (>= (+ (* 1 (and (_ bitOf x 1) (_ bitOf y 1))) (* 1 (- 1 (_ bitOf z 1))) 0) 3)) :rule cp_addition :premises (c15 c16))
; c18 : !r1 >= 0 : cp_literal
(step c18 (cl (>= (+ (* 1 (- 1 (and (_ bitOf x 1) (_ bitOf y 1)))) 0) 0)) :rule cp_literal)
; c19 : z1 >= 0 : cp_literal
(step c19 (cl (>= (+ (* 1 (_ bitOf z 1)) 0) 0)) :rule cp_literal)
; c20 : !z1 >= 2 : cp_addition c17 c18
(step c20 (cl (>= (+ (* 1 (- 1 (_ bitOf z 1))) 0) 2)) :rule cp_addition :premises (c17 c18))
; c21 : 0 >= 1 : cp_addition c19 c20
(step c21 (cl (>= 0 1)) :rule cp_addition :premises (c19 c20))
; UNSAT : cp_fail c21
(step c22 (cl) :rule cp_fail :premises (c21))