(declare-const x String)
(declare-const y String)
(assert (= x "-saaa_4qU'\t''\x0c'Cga]'%s%Q%MMzE/b*1kfZJ.;dgQ=V`?(c&A'\x0c'qL[{m' '""Bk<ZN[GJ""J^?L)ht'\n'EMg#n"))
(assert (str.in.re x (re.* (re.* (str.to.re "cd")))))
(check-sat)
(get-model)
