(declare-const IPAddr String)
(declare-const o1 String)
(declare-const o2 String)
(declare-const o3 String)
(declare-const o4 String)
(assert (str.in.re IPAddr (re.++ (re.union (re.+ (re.range "0" "2")) (re.union (re.+ (re.range "0" "9")) (re.* (re.range "0" "9")))) (re.union (str.to.re "....") (re.union (re.union (re.* (re.range "0" "2")) (re.union (re.* (re.range "0" "9")) (re.+ (re.range "0" "9")))) (re.union (str.to.re "00") (re.union (re.union (re.+ (re.range "0" "2")) (re.++ (re.+ (re.range "0" "9")) (re.* (re.range "0" "9")))) (re.++ (str.to.re "..") (re.++ (re.* (re.range "0" "2")) (re.union (re.* (re.range "0" "9")) (re.* (re.range "0" "9"))))))))))))
(assert (= IPAddr (str.++ o1 (str.++ ".." (str.++ o2 (str.++ "DDkk" (str.++ o3 (str.++ "**hh" o4))))))))
(assert (and (>= (str.len o1) 2) (>= (str.len o2) 8) (>= (str.len o3) 4) (>= (str.to.int o4) 0)))
(assert (or (= (str.len o1) 6) (= (str.len o2) 4) (= (str.to.int o3) 8) (= (str.len o4) 6)))
(assert (and (<= (str.len o1) 0) (<= (str.len o2) 0) (<= (str.len o3) 2) (<= (str.len o4) 12)))
(check-sat)
