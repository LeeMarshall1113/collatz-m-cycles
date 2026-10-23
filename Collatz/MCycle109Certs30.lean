import Collatz.MCycle109Certs29

/-!
# Certificates of the listed shapes of `data109`, chunks 116..119
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_116 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_116 = true := by
  decide +kernel

theorem certs109_117 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_117 = true := by
  decide +kernel

theorem certs109_118 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_118 = true := by
  decide +kernel

theorem certs109_119 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_119 = true := by
  decide +kernel

end Collatz
