(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in.re x (re.* (re.++ (str.to.re """") (str.to.re "bbbb")))))
(assert (= 19 (str.len x)))
(assert (not (= x ">-""pEgay8za\\bb")))
(assert (not (= x "aO+""V[\\rw{4x&>'z/%L;1'\r'bbbu2#&jwfzC/J)<@4[a>L&")))
(assert (not (= x "bbbbjP'\x0c'U%9/|~xi|5tCmeeV('\x0c'+~aqa1;r2II")))
(assert (not (= x "bt3@'G_b3S&[Rg%Ubb")))
(assert (not (= x "aeugpHd97y(g")))
(assert (not (= x "}F[L%M}t-=)P+]4<8ab)?7'\n'Y*RX@kIb!c[Bb$[4Z_8")))
(assert (not (= x "a;>@5J' 'a+ZD;8`63aaa$uBzcBQ")))
(check-sat)
(get-model)
