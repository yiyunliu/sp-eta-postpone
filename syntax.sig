PTm(VarPTm) : Type
PTag : Type
BTag : Type

nat : Type

PL : PTag
PR : PTag

PPi : BTag
PSig : BTag

PAbs : (bind PTm in PTm) -> PTm
PApp : PTm -> PTm -> PTm
PPair : PTm -> PTm -> PTm
PProj : PTag -> PTm -> PTm
PBind : BTag -> PTm -> (bind PTm in PTm) -> PTm
PUniv : nat -> PTm