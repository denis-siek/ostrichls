(set-logic QF_S)

(declare-fun a () String)
(declare-fun b () String)
(declare-fun c () String)
(declare-fun d () String)
(declare-fun e () String)
(declare-fun f () String)
(declare-fun x () String)

(assert (= x (str.++ a b)))
(assert (= x (str.++ c d)))
(assert (= x (str.++ e f)))
(assert (= c (str.++ d d)))
(assert (= f "123"))

(check-sat)
(get-model)