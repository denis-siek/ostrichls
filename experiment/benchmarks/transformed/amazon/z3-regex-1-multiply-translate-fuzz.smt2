(declare-const S String)
(assert (not (str.in.re S (re.++ (str.to.re "PPP}'\t'FyGF/9f;noonlZS""n""}") re.allchar))))
(assert (str.in.re S (re.union (re.union (re.union (str.to.re ";'\x0c'G' 'VPPMebpXB") re.allchar) (str.to.re "JGKLY}")) re.allchar)))
(check-sat)
(get-model)
(get-info :reason-unknown)
