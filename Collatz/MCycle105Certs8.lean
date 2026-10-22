import Collatz.MCycle105Certs7

/-!
# Certificates of the listed shapes of `data105`, chunks 28..31
-/

set_option Elab.async false

namespace Collatz

theorem certs105_28 : certsOK3 105 20 grid103 grid3_105 data105.certs shapes105_28 = true := by
  decide +kernel

theorem certs105_29 : certsOK3 105 20 grid103 grid3_105 data105.certs shapes105_29 = true := by
  decide +kernel

theorem certs105_30 : certsOK3 105 20 grid103 grid3_105 data105.certs shapes105_30 = true := by
  decide +kernel

theorem certs105_31 : certsOK3 105 20 grid103 grid3_105 data105.certs shapes105_31 = true := by
  decide +kernel

end Collatz
