(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.* (str.to.re "3Z\\3b"))))
(assert (str.in.re x (re.* (str.to.re "dcbd[#Oba"))))
(assert (> (str.len x) 28))
(assert (< (str.to.int x) 7))
(check-sat)
(get-model)
