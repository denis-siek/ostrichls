(set-logic QF_S)

(declare-fun a () String)
(declare-fun b () String)
(declare-fun c () String)
(declare-fun d () String)

(assert (= d (str.++ "xy" a)))

(assert (str.in.re a (re.+ (str.to.re "x"))))
(assert (str.in.re b (re.+ (str.to.re "y"))))
(assert (str.in.re c (re.+ (str.to.re "z"))))
(assert (str.in.re d (re.+ (str.to.re "xy"))))


(check-sat)
(get-model)