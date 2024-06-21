(set-logic QF_S)

(declare-fun a () String)
(declare-fun b () String)
(declare-fun c () String)
(declare-fun d () String)

(assert (str.in.re a (re.+ (str.to.re "y"))))
(assert (= a (str.++ b c)))
(assert (= "yx" (str.++ a d)))

(check-sat)
(get-model)