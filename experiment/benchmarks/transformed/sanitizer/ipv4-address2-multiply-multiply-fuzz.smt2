(declare-const IPAddr String)
(assert (>= (str.len IPAddr) 2))
(assert (<= (str.len IPAddr) 100))
(assert (str.in.re IPAddr (re.++ (re.++ (re.* (re.range "0" "2")) (re.++ (re.* (re.range "0" "9")) (re.* (re.range "0" "9")))) (re.union (str.to.re ".e<.") (re.union (re.union (re.+ (re.range "0" "2")) (re.union (re.* (re.range "0" "9")) (re.+ (re.range "0" "9")))) (re.++ (str.to.re "AGVmMC") (re.union (re.union (re.* (re.range "0" "2")) (re.union (re.* (re.range "0" "9")) (re.+ (re.range "0" "9")))) (re.union (str.to.re "mI,...") (re.union (re.+ (re.range "0" "2")) (re.++ (re.* (re.range "0" "9")) (re.* (re.range "0" "9"))))))))))))
(assert (not (str.in.re IPAddr (re.++ (re.++ (re.++ (str.to.re "2255") (re.range "0" "5")) (re.++ (re.union (str.to.re "22@_") (re.++ (re.range "0" "4") (re.range "0" "9"))) (re.union (re.opt (re.++ (str.to.re "0&") (str.to.re "11L<r@1"))) (re.union (re.range "0" "9") (re.opt (re.range "0" "9")))))) (re.++ (str.to.re "'\r'f[5A+5Jp;") (re.++ (re.union (re.union (str.to.re "2254'\t'e|5-6Uv'\r'") (re.range "0" "5")) (re.++ (re.++ (str.to.re "22zW0") (re.union (re.range "0" "4") (re.range "0" "9"))) (re.union (re.opt (re.++ (str.to.re "h]v(00") (str.to.re "t111"))) (re.union (re.range "0" "9") (re.opt (re.range "0" "9")))))) (re.++ (str.to.re ".nKSutz*g") (re.++ (re.++ (re.++ (str.to.re ":/9Dmq'\x0b'5") (re.range "0" "5")) (re.union (re.union (str.to.re "#.DQ""i1D2'\x0c''\x0b'&p") (re.++ (re.range "0" "4") (re.range "0" "9"))) (re.++ (re.opt (re.union (str.to.re "WJb-00") (str.to.re "11)W"))) (re.++ (re.range "0" "9") (re.opt (re.range "0" "9")))))) (re.++ (str.to.re "..") (re.union (re.++ (str.to.re "2q6") (re.range "0" "5")) (re.++ (re.++ (str.to.re "\\=3222") (re.++ (re.range "0" "4") (re.range "0" "9"))) (re.++ (re.opt (re.++ (str.to.re "cp") (str.to.re "|lMU"))) (re.union (re.range "0" "9") (re.opt (re.range "0" "9")))))))))))))))
(check-sat)
