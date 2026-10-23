import Collatz.MCycle109Certs26

/-!
# Certificates of the listed shapes of `data109`, chunks 104..107
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_104 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_104 = true := by
  decide +kernel

theorem certs109_105 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_105 = true := by
  decide +kernel

theorem certs109_106 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_106 = true := by
  decide +kernel

theorem certs109_107 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_107 = true := by
  decide +kernel

end Collatz
