(declare-const x String)
(assert (= x "{HLBB&"))
(assert (str.in.re x (re.++ (re.+ (str.to.re ".7xB")) (re.+ (str.to.re "#B&'\t'-")))))
(check-sat)
(get-model)
