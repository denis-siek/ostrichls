(set-logic QF_S)

(declare-fun a () String)
(declare-fun b () String)
(declare-fun c () String)
(declare-fun d () String)

(assert (= a (str.++ b c)))
(assert (= (str.++ a b) (str.++ d c)))

(assert (str.in.re a (re.+ (re.union (str.to.re "x") (str.to.re "y")))))
(assert (str.in.re c (re.+ (str.to.re "xyxy"))))
(assert (str.in.re b (re.+ (str.to.re "xy"))))

(check-sat)
(get-model)