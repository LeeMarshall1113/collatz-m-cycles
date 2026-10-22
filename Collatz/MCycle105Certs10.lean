import Collatz.MCycle105Certs9

/-!
# Certificates of the listed shapes of `data105`, chunks 36..39
-/

set_option Elab.async false

namespace Collatz

theorem certs105_36 : certsOK3 105 20 grid103 grid3_105 data105.certs shapes105_36 = true := by
  decide +kernel

theorem certs105_37 : certsOK3 105 20 grid103 grid3_105 data105.certs shapes105_37 = true := by
  decide +kernel

theorem certs105_38 : certsOK3 105 20 grid103 grid3_105 data105.certs shapes105_38 = true := by
  decide +kernel

theorem certs105_39 : certsOK3 105 20 grid103 grid3_105 data105.certs shapes105_39 = true := by
  decide +kernel

end Collatz
