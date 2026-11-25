# Слайдинг при обобщённой гладкости

- [Постановка задачи](<исследовательская задача.md>) описывает цель исследования и исходные статьи.
- [Статьи и переводы](papers/) и [аннотации](annot/) собраны отдельно. Обозначения вынесены в [заметку по статье Borodich и соавторов](annot/Borodich_et_al_2025_notation_ru.md).
- В [results](results/) находится [текст пути А](results/path_a_replacement.md) с формулировкой, доказательством и ссылками на Lean.
- В [архиве](archive/) по отдельным папкам собраны ранний путь А, пути Б и В, динамические веса и общие планы. [Сравнительный обзор](archive/theory_review/) включает ранний черновик LaTeX и его разборы.

## Формализация в Lean

Из каталога LeanLab команда `lake build` собирает весь проект, а `lake build LeanLab.PathA` проверяет путь А и его общие зависимости. [Точка входа проекта](LeanLab/LeanLab.lean)

- **PathA.** Расписание циклов, адаптивная рекурсия, зазор принятого прохода и итоговая теорема `Family.pathA_of_symmetric`. [Schedule](LeanLab/LeanLab/PathA/Schedule.lean) · [Pass](LeanLab/LeanLab/PathA/Pass.lean) · [Guarantees](LeanLab/LeanLab/PathA/Guarantees.lean) · [Restart](LeanLab/LeanLab/PathA/Restart.lean)
- **Common.** Симметричная гладкость, проекции, усреднение и общие леммы рекурсии. [Общие модули](LeanLab/LeanLab/Common/)
- **Variants.** Двухуровневый поиск, неускоренная и ускоренная схемы, рекурсия с фиксированной кривизной и многоуровневые динамические веса. [Остальные схемы](LeanLab/LeanLab/Variants/)

## GitHub configuration for LeanLab

To set up your new GitHub repository, follow these steps:

* Under your repository name, click **Settings**.
* In the **Actions** section of the sidebar, click "General".
* Check the box **Allow GitHub Actions to create and approve pull requests**.
* Click the **Pages** section of the settings sidebar.
* In the **Source** dropdown menu, select "GitHub Actions".

