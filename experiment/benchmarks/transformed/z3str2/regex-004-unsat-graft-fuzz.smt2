(declare-const x String)
(assert (= x "3qpjJ*kn9tG,' 'RfdEpgn=ee"))
(assert (str.in.re x (re.++ (re.* (re.* (str.to.re ""))) (str.to.re "bd"))))
(check-sat)
(get-model)
