-- Aggregator: importing this module forces elaboration of the ENTIRE
-- development — checker, faithfulness theorem, semantics, and the
-- operational layer.  `lake build` builds it by default, so a fresh clone
-- verifies every proof, not just the checker.  (Without this, nothing
-- imported Derivable/Semantics/Operational and the default target's
-- closure never elaborated them.)
import TPTND
import TPTND.Derivable
import TPTND.Semantics
import TPTND.Operational.RunSpace
import TPTND.Operational.Reduction
import TPTND.Operational.Convergence
import TPTND.Operational.TrustGuarantee
