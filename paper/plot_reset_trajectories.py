"""从轨迹 CSV 绘制双语论文共用的英文机制图。"""

from pathlib import Path
import csv
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.ticker import MultipleLocator, LogLocator, NullLocator

HERE = Path(__file__).resolve().parent
BLUE = "#226A98"
OCHRE = "#B66A24"


def main():
    with (HERE / "reset_trajectories.csv").open(encoding="utf-8", newline="") as stream:
        rows = list(csv.DictReader(stream))
    plt.rcParams.update({
        "font.family": "serif", "font.size": 9,
        "axes.labelsize": 9, "axes.titlesize": 9.5, "legend.fontsize": 8,
        "xtick.labelsize": 8, "ytick.labelsize": 8,
        "pdf.fonttype": 42, "ps.fonttype": 42,
        "lines.linewidth": 1.5,
    })
    fig, axs = plt.subplots(2, 2, figsize=(7.0, 4.65), sharex=True,
                            layout="constrained", gridspec_kw={"height_ratios": [1, 1.15]})
    for col, (family, title) in enumerate([
        ("pure", "Tilted pure stationary state"),
        ("diagonal", "Diagonal stationary state"),
    ]):
        values = [r for r in rows if r["family"] == family]
        t = np.array([float(r["t"]) for r in values])
        eps = float(values[0]["epsilon_star"])
        tc = float(values[0]["crossing"])
        a = np.array([float(r["a"]) for r in values])/eps
        target = np.array([float(r["epsilon"]) for r in values])/eps
        dq = np.array([float(r["D_quantum"]) for r in values])/eps
        dp = np.array([float(r["D_population"]) for r in values])/eps
        top, bottom = axs[:, col]
        top.plot(t, a, color=BLUE, label=r"Input $|0\rangle$")
        top.plot(t, target, color=OCHRE, label=r"Input $|1\rangle$")
        top.axhline(1, color="#BBBBBB", ls=":", lw=.6, zorder=0)
        selected = np.argmin(abs(t-1))
        top.plot([1, 1], [a[selected], target[selected]], "o", color="black", ms=3,
                 markerfacecolor="white", markeredgewidth=.7)
        top.set_ylim(.80, 1.38)
        top.set_title(title, pad=8)
        top.yaxis.set_major_locator(MultipleLocator(.2))
        bottom.plot(t, dq, color=BLUE, label=r"Trace distance $D_{\mathrm{tr}}$")
        bottom.plot(t, dp, color=OCHRE, label=r"Population distance $D_{\mathrm{pop}}$")
        bottom.set_yscale("log")
        bottom.set_ylim(.001, 100)
        bottom.yaxis.set_major_locator(LogLocator(base=10, numticks=6))
        bottom.yaxis.set_minor_locator(NullLocator())
        bottom.annotate(r"$D_{\mathrm{pop}}(t_c)=0$", xy=(tc, .00115), xytext=(tc+.15, .0030),
                        fontsize=8, color="#555555",
                        arrowprops=dict(arrowstyle="-", color="#777777", lw=.65))
        bottom.set_xlabel(r"Time $t/t_{\mathrm{r}}$")
        for row, ax in enumerate((top, bottom)):
            ax.axvline(tc, color="#777777", ls=(0, (2, 2)), lw=.8, zorder=0)
            ax.set_xlim(.78, 1.45)
            ax.xaxis.set_major_locator(MultipleLocator(.2))
            ax.spines["top"].set_visible(False)
            ax.spines["right"].set_visible(False)
            ax.tick_params(direction="out", length=3, width=.6)
            ax.text(.025, 1.015, f"({chr(97+2*row+col)})", transform=ax.transAxes,
                    va="bottom", ha="left", fontsize=9)
        top.text(tc+.01, 1.33, r"$t_c$", fontsize=9, color="#555555")
    axs[0, 0].set_ylabel(r"Population $P(0|j;t)/\epsilon_\star$")
    axs[1, 0].set_ylabel(r"Distance / $\epsilon_\star$")
    axs[0, 0].legend(loc="upper right", frameon=False)
    axs[1, 0].legend(loc="upper right", frameon=False)
    fig.savefig(HERE/"reset_trajectories.pdf")
    fig.savefig(HERE/"reset_trajectories.png", dpi=240)
    plt.close(fig)


if __name__ == "__main__":
    main()
