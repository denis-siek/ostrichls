(set-logic QF_S)

(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(declare-fun a () String)
(declare-fun b () String)

(assert (= x (str.replace y "e" z)))
(assert (= y "hello"))
(assert (str.in.re z ( re.+ (str.to.re "xy"))))
(assert (= a (str.++ z z)))
(assert (= b x))

(check-sat)
(get-model)