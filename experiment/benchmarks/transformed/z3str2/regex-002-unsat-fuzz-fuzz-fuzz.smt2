(declare-const x String)
(declare-const y String)
(assert (= x "'G>6''{+ojw#%4W>+d=!' '$\\DA$' '27*4'{x5QS:"))
(assert (str.in.re x (re.* (str.to.re ""))))
(check-sat)
(get-model)
