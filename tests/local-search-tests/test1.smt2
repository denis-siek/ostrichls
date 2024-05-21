(set-logic QF_S)

(declare-fun a () String)
(declare-fun b () String)
(declare-fun c () String)
(declare-fun d () String)

(assert (= (str.++ a (str.++ a b)) (str.++ d (str.++ "x" c))))

(check-sat)
(get-model)