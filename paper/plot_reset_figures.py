"""从随附 CSV 重绘论文中的两张图，不重新计算或优化构造。"""

from pathlib import Path
import csv

import numpy as np
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.ticker import FixedLocator, NullLocator, ScalarFormatter


HERE = Path(__file__).resolve().parent
BLUE = "#226A98"
OCHRE = "#B66A24"
DASHES = (0, (4, 3))


def read_curves(filename, families, columns):
    """仅将作图所需的坐标转成浮点数，避免极小概率发生下溢。"""
    curves = {family: [] for family in families}
    with (HERE / filename).open(newline="", encoding="utf-8") as stream:
        for row in csv.DictReader(stream):
            family = row["family"]
            if family in curves:
                curves[family].append(tuple(float(row[column]) for column in columns))
    return {family: np.asarray(values) for family, values in curves.items()}


def style_axes(ax):
    ax.spines["top"].set_visible(False)
    ax.spines["right"].set_visible(False)
    ax.tick_params(direction="out", length=3, width=0.6)
    ax.grid(axis="y", color="#D8D8D8", linewidth=0.5, alpha=0.7)
    ax.set_axisbelow(True)


def save_figure(fig, stem):
    # 固定物理尺寸；不使用紧裁剪，以保持单栏成图尺寸不变。
    fig.savefig(HERE / f"{stem}.pdf")
    fig.savefig(HERE / f"{stem}.png", dpi=300)
    plt.close(fig)


def plot_gain_comparison():
    curves = read_curves(
        "reset_gain_comparison.csv",
        ("pure", "diagonal"),
        ("actual_log_inverse_epsilon", "gain_fraction"),
    )
    fig, ax = plt.subplots(figsize=(3.4, 3.55), layout="constrained")
    for family, color, marker, label in (
        ("pure", BLUE, "o", "Pure stationary state"),
        ("diagonal", OCHRE, "s", "Diagonal stationary state"),
    ):
        values = curves[family]
        ax.plot(
            values[:, 0], values[:, 1], color=color, marker=marker,
            markevery=22, markersize=3.5, markerfacecolor="white",
            markeredgewidth=0.8, label=label,
        )

    x = curves["pure"][:, 0]
    ax.plot(x, 4 / (np.e * x), color=BLUE, ls=DASHES, lw=1.0,
            label=r"$4/(eL_\epsilon)$ (asymptotic)")
    ax.plot(x, 64 / (np.e**2 * x**2), color=OCHRE, ls=DASHES, lw=1.0,
            label=r"$64/(e^2L_\epsilon^2)$ (asymptotic)")
    ax.set_xscale("log")
    ax.set_yscale("log")
    ax.set_xlim(x[0], x[-1])
    ax.set_ylim(2e-7, 0.3)
    ax.set_xlabel(r"Actual error coordinate $L_\epsilon=\ln(1/\epsilon)$")
    ax.set_ylabel(r"Reversal fraction $\Delta/\epsilon$")
    ax.xaxis.set_major_locator(FixedLocator([10, 30, 100, 300, 1000]))
    ax.xaxis.set_major_formatter(ScalarFormatter())
    ax.xaxis.set_minor_locator(NullLocator())
    ax.yaxis.set_minor_locator(NullLocator())
    style_axes(ax)
    ax.legend(loc="lower left", frameon=False, fontsize=8.5,
              handlelength=2.5, labelspacing=0.45, borderpad=0.1,
              bbox_to_anchor=(0.02, 0.035))

    top = ax.secondary_xaxis("top")
    top.set_xticks([n * np.log(10) for n in (3, 10, 100, 1000)])
    top.set_xticklabels([r"$10^{-3}$", r"$10^{-10}$", r"$10^{-100}$", r"$10^{-1000}$"])
    top.xaxis.set_minor_locator(NullLocator())
    top.set_xlabel(r"Actual disturbance $\epsilon$", labelpad=5)
    top.tick_params(direction="out", length=3, width=0.6)
    save_figure(fig, "reset_gain_comparison")


def plot_convergence():
    curves = read_curves(
        "family_convergence.csv",
        ("pure", "aligned"),
        ("actual_log_inverse_epsilon", "scaled_log", "scaled_log_squared"),
    )
    fig, axes = plt.subplots(2, 1, figsize=(3.4, 4.6), layout="constrained")
    pure, diagonal = curves["pure"], curves["aligned"]

    axes[0].plot(pure[:, 0], pure[:, 1], color=BLUE,
                 label="Pure stationary state")
    axes[0].axhline(4 / np.e, ls=DASHES, lw=1.0, color="#555555",
                    label=r"$4/e$ (asymptotic)")
    axes[0].set_ylabel(r"$\Delta L_\epsilon/\epsilon$")
    axes[0].legend(loc="lower right", frameon=False, fontsize=9,
                   handlelength=2.4, borderpad=0.1)
    axes[0].text(0.025, 0.88, "(a)", transform=axes[0].transAxes,
                 va="top", fontweight="bold")

    axes[1].plot(diagonal[:, 0], diagonal[:, 2], color=OCHRE,
                 label="Diagonal stationary state")
    axes[1].axhline(64 / np.e**2, ls=DASHES, lw=1.0, color="#555555",
                    label=r"$64/e^2$ (asymptotic)")
    axes[1].set_ylabel(r"$\Delta L_\epsilon^2/\epsilon$")
    axes[1].legend(loc="upper right", frameon=False, fontsize=9,
                   handlelength=2.4, borderpad=0.1)
    axes[1].text(0.025, 0.97, "(b)", transform=axes[1].transAxes,
                 va="top", fontweight="bold")

    for ax in axes:
        ax.set_xscale("log", base=2)
        ax.set_xticks([20, 80, 320, 1280])
        ax.xaxis.set_major_formatter(ScalarFormatter())
        ax.xaxis.set_minor_locator(NullLocator())
        ax.set_xlabel(r"Actual error coordinate $L_\epsilon=\ln(1/\epsilon)$")
        ax.set_xlim(20, 2560)
        style_axes(ax)
    save_figure(fig, "reset_convergence")


def main():
    plt.rcParams.update({
        "font.family": "DejaVu Sans",
        "font.size": 9,
        "axes.labelsize": 9.5,
        "legend.fontsize": 9,
        "axes.linewidth": 0.7,
        "lines.linewidth": 1.6,
        "pdf.fonttype": 42,
    })
    plot_gain_comparison()
    plot_convergence()
    print("Redrew reset_gain_comparison.pdf/png and reset_convergence.pdf/png.")


if __name__ == "__main__":
    main()
