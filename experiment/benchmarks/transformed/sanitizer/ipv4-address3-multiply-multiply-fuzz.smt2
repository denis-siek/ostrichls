(declare-const IPAddr String)
(declare-const o1 String)
(declare-const o2 String)
(declare-const o3 String)
(declare-const o4 String)
(assert (str.in.re IPAddr (re.union (re.++ (re.+ (re.range "0" "2")) (re.++ (re.* (re.range "0" "9")) (re.+ (re.range "0" "9")))) (re.union (str.to.re "..") (re.union (re.union (re.+ (re.range "0" "2")) (re.union (re.* (re.range "0" "9")) (re.* (re.range "0" "9")))) (re.++ (str.to.re "->..x.]""") (re.++ (re.union (re.* (re.range "0" "2")) (re.union (re.* (re.range "0" "9")) (re.* (re.range "0" "9")))) (re.union (str.to.re "W..") (re.++ (re.* (re.range "0" "2")) (re.++ (re.* (re.range "0" "9")) (re.+ (re.range "0" "9"))))))))))))
(assert (= IPAddr (str.++ o1 (str.++ "<'\n'^" (str.++ o2 (str.++ "['\r'M" (str.++ o3 (str.++ ".'\r'%@{" o4))))))))
(assert (and (>= (str.to.int o1) 3) (>= (str.to.int o2) 7) (>= (str.to.int o3) 5) (>= (str.len o4) 8)))
(assert (or (= (str.to.int o1) 8) (= (str.to.int o2) 7) (= (str.len o3) 3) (= (str.len o4) 7)))
(assert (and (<= (str.len o1) 4) (<= (str.len o2) 7) (<= (str.to.int o3) 0) (<= (str.to.int o4) 15)))
(check-sat)
