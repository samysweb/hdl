export ISABELLE="$HOME/Software/Isabelle2025/bin/isabelle"
export ISABELLE_AFP_THYS="$HOME/Software/Isabelle2025/afp-Isabelle2025/thys/"


$ISABELLE build -d $ISABELLE_AFP_THYS -d . -v -b Heterogeneous_Dynamic_Logic

$ISABELLE build  -d $ISABELLE_AFP_THYS -d . -d diff-dyn-theory -v -b Differential_Dynamic_Theory
