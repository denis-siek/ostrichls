(declare-const IPAddr String)
(declare-const o1 String)
(declare-const o2 String)
(declare-const o3 String)
(declare-const o4 String)
(assert (str.in.re IPAddr (re.union (re.union (re.+ (re.range "0" "2")) (re.++ (re.+ (re.range "0" "9")) (re.* (re.range "0" "9")))) (re.union (str.to.re "") (re.++ (re.union (re.* (re.range "0" "2")) (re.union (re.* (re.range "0" "9")) (re.* (re.range "0" "9")))) (re.++ (str.to.re "/") (re.++ (re.++ (re.+ (re.range "0" "2")) (re.++ (re.* (re.range "0" "9")) (re.+ (re.range "0" "9")))) (re.union (re.* (re.range "0" "9")) (re.++ (re.+ (re.range "0" "2")) (re.++ (re.+ (re.range "0" "9")) (str.to.re ":")))))))))))
(assert (= IPAddr (str.++ o1 (str.++ "" (str.++ o2 "(")))))
(assert (and (>= (str.to.int o1) 2) (>= (str.to.int o2) 1) (>= (str.to.int o3) 1) (>= (str.to.int o4) 2)))
(assert (or (= (str.len o1) 0) (= (str.to.int o2) (str.len o2)) (= (str.len o3) 1) (= (str.to.int o4) 1)))
(assert (and (<= (str.len o1) 2) (<= 2 5) (<= (str.to.int o3) 2) (<= (str.to.int o4) 6)))
(check-sat)
