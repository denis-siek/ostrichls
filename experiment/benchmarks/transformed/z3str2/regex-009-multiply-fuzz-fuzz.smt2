(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (str.to.re ";W:5*k;rd&1'\x0b''\t'its}1OezG,Df$~?4h:s)R'\n']e!eI_,:c4!6c'J4"))))
(assert (str.in.re x (re.* (str.to.re "37aJ8(.cp2r{F2knr7'`^?>'LB'\t'vdiI_[h+FqYD`&(Ei\\,aT'\x0b'YT^1yU{h'\n'_vFz>*96uwu4h|EOJpS;Zc)'\r'Ou'\r'fi+v<zQ%Pl=QPJ' '31D+wqQFMw0[BM7~0-'\r'Wcyh7OJfX3o'nSAz%UzdaS~B#T{U'\n'}'\x0c'' '_J$MP""[1L~szY'G'\n'+y'\n'B8i}O2C^RUr;nv@10gr'\x0b'hW6rIFW,b#""Cr0AZmB'\x0b'W5tU*QQ5a6H/7jl}#hR?Ai:\\_~"))))
(assert (> (str.to.int x) 18))
(assert (< (str.len x) 46))
(check-sat)
(get-model)
