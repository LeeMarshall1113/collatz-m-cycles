import Collatz.MCycle104Certs6

/-!
# Certificates of the listed shapes of `data104`, chunks 24..27
-/

set_option Elab.async false

namespace Collatz

theorem certs104_24 : certsOK3 104 20 grid103 grid3_105 data104.certs shapes104_24 = true := by
  decide +kernel

theorem certs104_25 : certsOK3 104 20 grid103 grid3_105 data104.certs shapes104_25 = true := by
  decide +kernel

theorem certs104_26 : certsOK3 104 20 grid103 grid3_105 data104.certs shapes104_26 = true := by
  decide +kernel

theorem certs104_27 : certsOK3 104 20 grid103 grid3_105 data104.certs shapes104_27 = true := by
  decide +kernel

end Collatz
