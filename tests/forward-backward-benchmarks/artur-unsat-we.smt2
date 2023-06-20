(set-logic QF_S)
(declare-fun X () String)
(declare-fun A () String)
(declare-fun B () String)
(declare-fun C () String)
(declare-fun D () String)
(declare-fun E () String)

(assert (= X (str.++ A B C)))
(assert (= C (str.++ "b" D)))
(assert (= B (str.++ "a" E)))
(assert (= (str.++ X X) (str.++ A A B B C C)))
(assert (= (str.++ X X X) (str.++ A A A B B B C C C)))

(check-sat)
