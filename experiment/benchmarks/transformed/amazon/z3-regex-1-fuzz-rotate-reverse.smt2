(declare-const S String)
(assert (not (str.in.re S (re.++ re.allchar (str.to.re "69+L.jQ7I''' '''G^:Ka")))))
(assert (str.in.re S (re.union re.allchar (re.++ (re.union (str.to.re "1a") re.allchar) (str.to.re ".T}b`")))))
(check-sat)
(get-model)
(get-info :reason-unknown)
