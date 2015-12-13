
(set-info :source |

encoding frst znth conclusion of body_swap in verif_swap 

 notes:
 - extracting  forall a i v, len a is equal to len store a i v explicitely (at every store)
 - We only reason about in-bound array stores. upd_znth generates store hypothesis, in-bound then length implication and in-bound in the goal
 - doesn't seem possible to encode len as function since it's domain is not a base type, using Ints instead 
|)

(set-info :smt-lib-version 2.0)
(set-info :status unsat)

(set-logic QF_AUFLIA)
(declare-fun a () (Array Int Int))
(declare-fun len_a () Int)
(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun size () Int)
(declare-fun undef () Int)

(declare-fun len_lspp () Int)
(declare-fun len_lsp () Int)



(assert (not (= undef (select a j))))

(assert (not (= undef (select a i))))

(assert (let ((?id (select a j)))
         (=> (not (= undef ?id)) (and (<= 0 j) (< j len_a)))))

(assert (let ((?id0 (select a i)))
         (=> (not (= undef ?id0)) (and (<= 0 i) (< i len_a)))))
	 
(assert (and (<= 0 i) (< i size)))
(assert (and (<= 0 j) (< j size)))





(assert (let ((?saj  (select a j)))
        (let ((?lspp (store a i ?saj))
	      (?sai (select a i)))
	 (let ((?lsp (store ?lspp j ?sai)))
	   (let ((?ls (select ?lsp i))
	         (?rs (select a j)))
	   (and (=> (and (<= 0 i) (< i len_a)) (= len_lspp len_a))
	   (and (=> (and (<= 0 j) (< j len_lspp)) (= len_lsp len_lspp))
              (not 
		    (and (= ?ls ?rs)
		    (and (=> (not (= ?saj 0)) (and (<= 0 j) (< j len_a)))
		    (and (=> (not (= ?saj 0)) (and (<= 0 i) (< i len_a)))
		    (and (=> (not (= ?ls 0)) (and (<= 0 i) (< i len_lsp)))
		    (and (=> (not (= ?rs 0)) (and (<= 0 j) (< j len_a)))
		     (and (and (<= 0 i) (< i len_a))
		     (and (<= 0 j) (< j len_lspp))))))))))))))))

(check-sat)
(exit)


