(declare-const IPAddr String)
(declare-const o1 String)
(declare-const o2 String)
(declare-const o3 String)
(declare-const o4 String)
(assert (str.in.re IPAddr (re.union (re.++ (re.+ (re.range "0" "2")) (re.++ (re.+ (re.range "0" "9")) (re.+ (re.range "0" "9")))) (re.++ (str.to.re ",,") (re.++ (re.union (re.* (re.range "0" "2")) (re.union (re.* (re.range "0" "9")) (re.+ (re.range "0" "9")))) (re.++ (str.to.re "vv") (re.union (re.union (re.+ (re.range "0" "2")) (re.++ (re.* (re.range "0" "9")) (re.+ (re.range "0" "9")))) (re.++ (str.to.re "HH") (re.++ (re.* (re.range "0" "2")) (re.union (re.+ (re.range "0" "9")) (re.* (re.range "0" "9"))))))))))))
(assert (= IPAddr (str.++ o1 (str.++ "TT" (str.++ o2 (str.++ ",," (str.++ o3 (str.++ "" o4))))))))
(assert (and (>= (str.len o1) 0) (>= (str.to.int o2) 2) (>= (str.to.int o3) 0) (>= (str.len o4) 4)))
(assert (or (= (str.to.int o1) 0) (= (str.len o2) 0) (= (str.len o3) 2) (= (str.len o4) 2)))
(assert (and (<= (str.to.int o1) 4) (<= (str.len o2) 10) (<= (str.to.int o3) 10) (<= (str.len o4) 8)))
(check-sat)
