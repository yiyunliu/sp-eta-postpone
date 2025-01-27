PTm(VarPTm) : Type
PTag : Type
Ty : Type

Fun : Ty -> Ty -> Ty
Prod : Ty -> Ty -> Ty
Void : Ty

PL : PTag
PR : PTag

PAbs : (bind PTm in PTm) -> PTm
PApp : PTm -> PTm -> PTm
PPair : PTm -> PTm -> PTm
PProj : PTag -> PTm -> PTm
