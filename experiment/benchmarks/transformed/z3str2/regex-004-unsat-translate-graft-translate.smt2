(declare-const x String)
(assert (= x "Ezz[zzzz'\n'zzbzz'\n'zzbx"))
(assert (str.in.re x (re.union (str.to.re "zz'\n'zzbx") (re.* (re.* (str.to.re "Ezz[zzzz'\n'zzb"))))))
(check-sat)
(get-model)
