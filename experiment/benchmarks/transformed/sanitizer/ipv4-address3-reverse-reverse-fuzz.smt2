(declare-const IPAddr String)
(declare-const o1 String)
(declare-const o2 String)
(declare-const o3 String)
(declare-const o4 String)
(assert (str.in.re IPAddr (re.union (re.++ (re.* (re.range "0" "2")) (re.++ (re.+ (re.range "0" "9")) (re.+ (re.range "0" "9")))) (re.++ (str.to.re "") (re.++ (re.++ (re.* (re.range "0" "2")) (re.++ (re.* (re.range "0" "9")) (re.* (re.range "0" "9")))) (re.++ (str.to.re ".") (re.union (re.union (re.* (re.range "0" "2")) (re.++ (re.+ (re.range "0" "9")) (re.+ (re.range "0" "9")))) (re.++ (str.to.re "*") (re.union (re.+ (re.range "0" "2")) (re.++ (re.* (re.range "0" "9")) (re.+ (re.range "0" "9"))))))))))))
(assert (= IPAddr (str.++ o1 (str.++ "." (str.++ o2 (str.++ "" (str.++ o3 (str.++ "." o4))))))))
(assert (and (>= (str.to.int o1) 1) (>= (str.len o2) 2) (>= (str.to.int o3) 1) (>= (str.len o4) 0)))
(assert (or (= (str.to.int o1) 1) (= (str.to.int o2) 0) (= (str.len o3) 0) (= (str.len o4) 0)))
(assert (and (<= (str.len o1) 4) (<= (str.len o2) 3) (<= (str.len o3) 5) (<= (str.len o4) 3)))
(check-sat)
