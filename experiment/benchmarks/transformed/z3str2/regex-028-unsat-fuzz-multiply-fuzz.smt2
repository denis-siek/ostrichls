(declare-const x String)
(declare-const y String)
(assert (str.in.re x (re.+ (str.to.re "abb"))))
(assert (str.in.re x (re.* (str.to.re "aba&k"))))
(assert (str.in.re x (re.* (str.to.re "6hCu^'\t'8'\r'Cz>34:n),'\x0c''\n'8T#O>tN' '*M<u^wYk&OC|PKyn'\r'S$=wmtr@""""G*~^' ''72HsZePzW<'\r'tMMU==m?'\r'tV'\t'' 'B9'\n'ZhL;;?<aIGrY3~v]""#b4q&^qom'\r'\\Muy\\GTZtB^J'Yt9g[u6jVYi^HC-^xQ607-6WfL=zriZ;f9#:I_"))))
(assert (> (str.to.int x) 7))
(check-sat)
(get-model)
