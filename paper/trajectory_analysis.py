"""计算已有两类构造的全时间轨迹，并与独立 GKSL 指数核对。"""

from pathlib import Path
import csv
import json
import numpy as np
from scipy.linalg import expm
from scipy.optimize import brentq

HERE = Path(__file__).resolve().parent
TARGET = 1e-4


def pure(L):
    p = np.exp(-L)
    A = L + np.log(L) + 1 - np.log(4)
    B = A / L
    U = np.array([[np.sqrt(1-p), np.sqrt(p)], [-np.sqrt(p), np.sqrt(1-p)]])
    J = U @ np.array([[-np.sqrt(B), 0], [np.sqrt(A), 0]]) @ U.T
    M = np.array([[-A, 0], [-np.sqrt(A*B), -(A+B)/2]])
    return dict(family="pure", p=p, nu=0., A=A, B=B, M=M, J=J, H=np.zeros((2, 2)), U=U)


def diagonal(L):
    nu = np.exp(-L)
    chi = np.sqrt(nu/(1-nu))
    tau = 2/L
    alpha = 1 + chi**2
    beta = ((1+chi)**2 + tau)/2
    b = 2*np.sqrt(tau)*chi/(1-chi)
    c = -np.sqrt(tau)*alpha/(1-chi)
    gap = np.sqrt((alpha-beta)**2 + 4*b*c)
    s = 2*b*c/(alpha-beta+gap)
    k = s/gap
    fast, slow = alpha+s, beta-s
    A = np.log(fast*(1-k)/(-slow*k))/gap
    B = tau*A
    h = np.sqrt(A*B)*(nu+chi/2)/(1-2*nu)
    J = np.array([[-np.sqrt(B), -chi*np.sqrt(A)], [np.sqrt(A), 0]])
    H = np.array([[0, 1j*h], [-1j*h, 0]])
    M = A*np.array([[-alpha, b], [c, -beta]])
    return dict(family="diagonal", p=0., nu=nu, A=A, B=B, M=M, J=J, H=H, U=np.eye(2))


def reduced(model, t):
    p, nu = model["p"], model["nu"]
    v, w = 1-2*p, 2*np.sqrt(p*(1-p))
    K = expm(model["M"]*t)
    u, z = K @ np.array([v, w])
    q, coherence = v*u+w*z, -w*u+v*z
    u1, z1 = K @ np.array([p-nu, -w/2])
    eps = nu + (1-2*nu)*p + v*u1 + w*z1
    return dict(t=t, q=q, coherence=coherence, D_quantum=np.hypot(q, coherence),
                D_population=abs(q), epsilon=eps, a=eps+q)


def liouvillian(model):
    # 直接对四个矩阵单位作用，不借用二维约化的向量化公式。
    J, H = model["J"], model["H"]
    Q = J.conj().T @ J
    result = np.empty((4, 4), dtype=complex)
    for col in range(4):
        X = np.zeros((2, 2), dtype=complex)
        X.flat[col] = 1
        dX = -1j*(H@X-X@H) + J@X@J.conj().T - (Q@X+X@Q)/2
        result[:, col] = dX.ravel()
    return result


def direct(model, t):
    E = expm(liouvillian(model)*t)
    rho0, rho1 = E[:, 0].reshape(2, 2), E[:, 3].reshape(2, 2)
    delta = rho0-rho1
    vals = np.linalg.eigvalsh(delta)
    return dict(q=float(delta[0, 0].real), coherence=float(delta[0, 1].real),
                D_quantum=float(np.sum(abs(vals))/2), epsilon=float(rho1[0, 0].real),
                a=float(rho0[0, 0].real))


def solve_model(builder, target):
    L = brentq(lambda L: reduced(builder(L), 1)["epsilon"]-target,
               np.log(1/target)-.2, np.log(1/target)+.2, xtol=1e-13)
    model = builder(L)
    model["L"] = L
    model["epsilon_star"] = reduced(model, 1)["epsilon"]
    model["crossing"] = brentq(lambda t: reduced(model, t)["q"], .2, 1.1)
    rates = np.sort(-np.linalg.eigvals(model["M"]))
    model["slow_rate"], model["fast_rate"] = rates
    model["reversal_peak"] = model["crossing"] + np.log(rates[1]/rates[0])/(rates[1]-rates[0])
    return model


def main():
    models = [solve_model(builder, TARGET) for builder in (pure, diagonal)]
    rows, report = [], {}
    for model in models:
        tc = model["crossing"]
        tgrid = np.unique(np.r_[np.linspace(0, 2, 1001), tc, 1.])
        for t in tgrid:
            row = reduced(model, t)
            row.update(family=model["family"], epsilon_star=model["epsilon_star"], crossing=tc)
            row["q_half_dephased"] = row["q"] if t<tc else row["q"]/2
            row["q_fully_dephased"] = row["q"] if t<tc else 0.
            rows.append(row)
        maxerr = 0.
        for t in np.r_[np.linspace(0, 2, 51), tc, 1.]:
            actual, expected = direct(model, t), reduced(model, t)
            maxerr = max(maxerr, max(abs(actual[k]-expected[k]) for k in actual))
        L4 = liouvillian(model)
        stationary = model["U"] @ np.diag([model["nu"], 1-model["nu"]]) @ model["U"].T
        residual = np.max(abs(L4@stationary.ravel()))
        delta_tc = expm(L4*tc)@np.array([1., 0., 0., -1.])
        pulse_errors = []
        for lam in (0., .25, .5, 1.):
            dephased = delta_tc.copy()
            dephased[[1, 2]] *= lam
            for t in np.linspace(tc, 2, 31):
                post = expm(L4*(t-tc))@dephased
                pulse_errors.append(abs(post[0].real-lam*reduced(model, t)["q"]))
        values = [reduced(model, t)["D_quantum"] for t in tgrid]
        report[model["family"]] = {
            k: float(model[k]) for k in ("L", "p", "nu", "A", "B", "epsilon_star", "crossing",
                                         "slow_rate", "fast_rate", "reversal_peak")
        }
        report[model["family"]].update(
            at_crossing=reduced(model, tc), at_readout=reduced(model, 1),
            largest_direct_reduced_error=float(maxerr), stationary_residual=float(residual),
            largest_trace_distance_increment=float(np.max(np.diff(values))),
            partial_dephasing_identity_error=float(max(pulse_errors)),
        )
    with (HERE/"reset_trajectories.csv").open("w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    (HERE/"trajectory_checks.json").write_text(json.dumps(report, indent=2), encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
