(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (= (str.++ x y) (str.++ m n)))
(assert (str.in.re n (re.+ (str.to.re """nee+'\r'IN~52w'\t'hWhmf'\x0c'4:,}Sy4""Z'<3-H""gO`<?'(OOd(8+b&mbBZd*?F'\n'Xr<gji6''\x0c'm0*X5&B>sT$TZ'@8(tV}eq54A}-%N]3P%u,'\n'3eh6;4+n}^x?j:5.#{1z~CY'\n'.'\n'z!wN13m'\x0b'STrc'\t'S<'\n'[B[&"))))
(assert (> (str.len x) (str.to.int m)))
(check-sat)
(get-model)
