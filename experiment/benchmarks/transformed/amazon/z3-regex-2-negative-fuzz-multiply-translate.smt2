(declare-const S String)
(assert (str.in.re S (re.union (str.to.re "'\x0b''\x0b'``00____") re.allchar)))
(assert (not (str.in.re S (re.union (re.++ (re.++ (str.to.re "NNNN88") re.allchar) (str.to.re "__88ii'\t''\t'")) re.allchar))))
(check-sat)
(get-model)
