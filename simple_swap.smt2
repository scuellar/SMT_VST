(set-logic QF_AUFLIA)
(set-info :source |
let temp1 = a [i] in
let v0 = (store a i (select a j)) in
let v1 = (store v0 j temp1) in
    a[i] = v1[j] and  a[j] = v1[i]
|)

(set-info :smt-lib-version 2.0)
(set-info :status unsat)
(declare-fun a () (Array Int Int))
(declare-fun i () Int)
(declare-fun j () Int)

(assert (let ((?t (select a i))
             (?v0 (store a i (select a j))))
        (let ((?v1 (store ?v0 j ?t)))
	     (not (and (= (select a i) (select ?v1 j))
	               (= (select a j) (select ?v1 i)))))))



	 (check-sat)
(exit)
