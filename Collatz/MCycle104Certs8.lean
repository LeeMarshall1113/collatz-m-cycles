import Collatz.MCycle104Certs7

/-!
# Certificates of the listed shapes of `data104`, chunks 28..30
-/

set_option Elab.async false

namespace Collatz

theorem certs104_28 : certsOK3 104 20 grid103 grid3_105 data104.certs shapes104_28 = true := by
  decide +kernel

theorem certs104_29 : certsOK3 104 20 grid103 grid3_105 data104.certs shapes104_29 = true := by
  decide +kernel

theorem certs104_30 : certsOK3 104 20 grid103 grid3_105 data104.certs shapes104_30 = true := by
  decide +kernel

end Collatz
