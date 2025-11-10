theory Test
  imports
    Main
    "SemiRingFOL"
    "HavocDynamicLogic"
    "KATDynamicLogic"
    "NatKATDynamicLogic"
    "SemiRingDL"
begin

term "''test''"

term "(''test'':=(Const (1::nat)))"

term "(( (''test'':=(Const (1::nat)));(''test'':=*) )*)"

term
  "(Less (Const 0) (Var a)) \<Rrightarrow> (\<lbrakk> (( ((Var a):=*);((Var a):=*) )*) \<rbrakk> (Less (Const 0) (Var a)))"

end