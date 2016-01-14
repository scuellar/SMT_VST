
(set-info :source |

encoding first conclusion of body_swap in verif_swap 

 notes:
 - doesn't seem possible to encode len as function since it's domain is not a base type, using Ints instead 
|)

(set-info :smt-lib-version 2.0)
(set-info :status unsat)

(set-logic QF_AUFLIA)
(declare-fun a () (Array Int Int))

(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun size () Int)
(declare-fun dI () Int)

(declare-fun saj () Int)
(declare-fun sai () Int)
(declare-fun lspp () (Array Int Int))
(declare-fun lsp () (Array Int Int))
(declare-fun rs () Int)
(declare-fun ls () Int)

(declare-fun len_a () Int)
(declare-fun len_lspp () Int)
(declare-fun len_lsp () Int)




(assert (not (= dI (select a j))))

(assert (not (= dI (select a i))))

(assert (let ((?id (select a j)))
         (=> (not (= dI ?id)) (and (<= 0 j) (< j len_a)))))

(assert (let ((?id0 (select a i)))
         (=> (not (= dI ?id0)) (and (<= 0 i) (< i len_a)))))
	 
(assert (and (<= 0 i) (< i size)))
(assert (and (<= 0 j) (< j size)))


(assert
      (and (and (=> (and (<= 0 j) (< j len_a)) (= saj (select a j)))
      	        (=> (not (and (<= 0 j) (< j len_a))) (= saj dI)))
      (and (= lspp (store a i saj))    
      (and (=> (and (<= 0 i) (< i len_a)) (= len_lspp len_a))
      (and (and (=> (and (<= 0 i) (< i len_a)) (= sai (select a i)))
                (=> (not (and (<= 0 i) (< i len_a))) (= sai dI)))
      (and (= lsp (store lspp j sai))
      (and (=> (and (<= 0 j) (< j len_lspp)) (= len_lsp len_lspp))
      (and (and (=> (and (<= 0 i) (< i len_lsp)) (= ls (select lsp i)))
                (=> (not (and (<= 0 i) (< i len_lsp))) (= ls dI)))
      (and (and (=> (and (<= 0 j) (< j len_a)) (= rs (select a j)))
                (=> (not (and (<= 0 j) (< j len_a))) (= rs dI)))
       (not (and (= ls rs))))))))))))
       

(check-sat)
(exit)


