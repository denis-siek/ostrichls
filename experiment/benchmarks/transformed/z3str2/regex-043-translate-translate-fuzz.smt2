(declare-const x String)
(declare-const y String)
(declare-const m String)
(declare-const n String)
(assert (str.in.re x (re.+ (re.union (str.to.re "3") (str.to.re "''\x0c''")))))
(assert (= 0 (str.len x)))
(assert (not (= x "E'\x0c'i{dWtx&%f''D5")))
(assert (not (= x "SHk%o'\x0c''\r'")))
(assert (not (= x "'\x0c'!/'\t'a' ''\x0b'nCc4")))
(assert (not (= x "=(6M' 'vp|<?=@=.Z|0-3'")))
(assert (not (= x "EYF,'\x0b'M")))
(assert (not (= x "'\x0c'3\\C\\:vE''\x0c''")))
(assert (not (= x "^/D")))
(check-sat)
(get-model)
