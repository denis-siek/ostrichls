(declare-const S String)
(assert (not (str.in.re S (re.++ (str.to.re "aabb<<$$LLWWLLpp") re.allchar))))
(assert (str.in.re S (re.++ (re.union (re.++ (str.to.re "aa") re.allchar) (str.to.re "bbbbbb")) re.allchar)))
(check-sat)
(get-model)
(get-info :reason-unknown)
