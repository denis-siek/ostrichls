(declare-const x String)
(assert (= x "deabu'\x0c'ah{BApRDoMQ=KXL=QDvO#n"))
(assert (str.in.re x (re.+ (re.++ (str.to.re "h:Ggy") (str.to.re "s1d")))))
(check-sat)
(get-model)
