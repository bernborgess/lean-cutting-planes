(set-option :produce-proofs true)

; Set the logic to quantifier-free bitvectors
(set-logic QF_BV)

; Declare 2-bit bitvector variables x and y
(declare-fun x () (_ BitVec 2))
(declare-fun y () (_ BitVec 2))

; Assert that x is equal to binary 10
(assert (= x #b10))

; Assert that the bitwise AND of x and y equals binary 01
(assert (= (bvand x y) #b01))

; Check for satisfiability
(check-sat)

; Produce certificate
(get-proof)