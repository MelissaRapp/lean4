/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "runtime/flet.h"
#include "kernel/type_checker.h"
#include "kernel/instantiate.h"
#include "library/util.h"
#include "library/constants.h"
#include "library/compiler/lc_util.h"

namespace lean {
class csimp_fn {
    type_checker::state m_st;
    local_ctx           m_lctx;
    buffer<expr>        m_fvars;
    name                m_x;
    unsigned            m_next_idx{1};

    environment const & env() const { return m_st.env(); }

    name_generator & ngen() { return m_st.ngen(); }

    expr find(expr const & e, bool skip_mdata = true) const {
        if (is_fvar(e)) {
            if (optional<local_decl> decl = m_lctx.find_local_decl(e)) {
                if (optional<expr> v = decl->get_value())
                    return find(*v);
            }
        } else if (is_mdata(e) && skip_mdata) {
            return find(mdata_expr(e));
        }
        return e;
    }

    bool is_atom(expr const & e) {
        switch (e.kind()) {
        case expr_kind::FVar: case expr_kind::Const: case expr_kind::Lit:
            return true;
        default:
            return false;
        }
    }

    expr infer_type(expr const & e) { return type_checker(m_st, m_lctx).infer(e); }

    name next_name() {
        /* Remark: we use `m_x.append_after(m_next_idx)` instead of `name(m_x, m_next_idx)`
           because the resulting name is confusing during debugging: it looks like a projection application.
           We should replace it with `name(m_x, m_next_idx)` when the compiler code gets more stable. */
        name r = m_x.append_after(m_next_idx);
        m_next_idx++;
        return r;
    }

    expr mk_let_decl(expr const & e) {
        expr type = infer_type(e);
        expr fvar = m_lctx.mk_local_decl(ngen(), next_name(), type, e);
        m_fvars.push_back(fvar);
        return fvar;
    }

    expr visit_let(expr e) {
        buffer<expr> let_fvars;
        while (is_let(e)) {
            expr new_type = instantiate_rev(let_type(e), let_fvars.size(), let_fvars.data());
            expr new_val  = visit(instantiate_rev(let_value(e), let_fvars.size(), let_fvars.data()));
            if (is_atom(new_val)) {
                let_fvars.push_back(new_val);
            } else {
                name n = is_internal_name(let_name(e)) ? next_name() : let_name(e);
                expr new_fvar = m_lctx.mk_local_decl(ngen(), n, new_type, new_val);
                let_fvars.push_back(new_fvar);
                m_fvars.push_back(new_fvar);
            }
            e = let_body(e);
        }
        return visit(instantiate_rev(e, let_fvars.size(), let_fvars.data()));
    }

    expr visit_lambda(expr e) {
        lean_assert(is_lambda(e));
        expr r;
        flet<local_ctx> save_lctx(m_lctx, m_lctx);
        unsigned m_fvars_init_size = m_fvars.size();
        buffer<expr> binding_fvars;
        while (is_lambda(e)) {
            /* Types are ignored in compilation steps. So, we do not invoke visit for d. */
            expr new_d    = instantiate_rev(binding_domain(e), binding_fvars.size(), binding_fvars.data());
            expr new_fvar = m_lctx.mk_local_decl(ngen(), binding_name(e), new_d, binding_info(e));
            binding_fvars.push_back(new_fvar);
            e = binding_body(e);
        }
        expr new_body = visit(instantiate_rev(e, binding_fvars.size(), binding_fvars.data()));
        new_body      = m_lctx.mk_lambda(m_fvars.size() - m_fvars_init_size, m_fvars.data() + m_fvars_init_size, new_body);
        m_fvars.shrink(m_fvars_init_size);
        return m_lctx.mk_lambda(binding_fvars, new_body);
    }

    expr visit_proj(expr const & e) {
        expr s = find(proj_expr(e));
        if (is_constructor_app(env(), s)) {
            buffer<expr> args;
            expr const & k        = get_app_args(s, args);
            constructor_val k_val = env().get(const_name(k)).to_constructor_val();
            lean_assert(k_val.get_nparams() + proj_idx(e).get_small_value() < args.size());
            return args[k_val.get_nparams() + proj_idx(e).get_small_value()];
        }
        return e;
    }

    bool is_cases_app(expr const & e) {
        expr const & fn = get_app_fn(e);
        return is_constant(fn) && is_cases_on_recursor(env(), const_name(fn));
    }

    expr reduce_cases_cases(expr const & c, buffer<expr> const & args, inductive_val const & I_val, expr const & major) {
        // TODO(Leo)
        return mk_app(c, args);
    }

    expr reduce_cases_cnstr(expr const & c, buffer<expr> const & args, inductive_val const & I_val, expr const & major) {
        lean_assert(is_constructor_app(env(), major));
        unsigned nparams = I_val.get_nparams();
        names cnstrs     = I_val.get_cnstrs();
        buffer<expr> k_args;
        expr const & k   = get_app_args(major, k_args);
        lean_assert(is_constant(k));
        lean_assert(nparams <= k_args.size());
        unsigned first_minor_idx = I_val.get_nparams() + 1 /* typeformer/motive */ + I_val.get_nindices() + 1 /* major */;
        for (unsigned i = first_minor_idx; i < args.size(); i++) {
            lean_assert(!empty(cnstrs));
            if (head(cnstrs) == const_name(k)) {
                return beta_reduce(args[i], k_args.size() - nparams, k_args.data() + nparams);
            }
            cnstrs = tail(cnstrs);
        }
        lean_unreachable();
    }

    expr visit_cases(expr const & e) {
        buffer<expr> args;
        expr const & c = get_app_args(e, args);
        lean_assert(is_constant(c));
        inductive_val I_val      = env().get(const_name(c).get_prefix()).to_inductive_val();
        unsigned major_idx       = I_val.get_nparams() + 1 /* typeformer/motive */ + I_val.get_nindices();
        lean_assert(major_idx < args.size());
        expr const & major       = find(args[major_idx]);
        if (is_constructor_app(env(), major)) {
            return reduce_cases_cnstr(c, args, I_val, major);
        } else if (is_cases_app(major)) {
            return reduce_cases_cases(c, args, I_val, major);
        } else {
            return e;
        }
    }

    expr beta_reduce(expr fn, unsigned nargs, expr const * args) {
        unsigned i = 0;
        while (is_lambda(fn) && i < nargs) {
            i++;
            fn = binding_body(fn);
        }
        expr r = visit(instantiate_rev(fn, i, args));
        lean_assert(!is_let(r));
        if (is_lambda(r)) {
            lean_assert(i == nargs);
            return r;
        } else {
            if (!is_atom(r))
                r = mk_let_decl(r);
            return visit(mk_app(r, nargs - i, args + i));
        }
    }

    expr beta_reduce(expr fn, expr const & e) {
        lean_assert(is_lambda(fn));
        lean_assert(is_eqp(find(get_app_fn(e)), fn));
        buffer<expr> args;
        get_app_args(e, args);
        return beta_reduce(fn, args.size(), args.data());
    }

    expr distrib_app_cases(expr const & fn, expr const & e) {
        lean_assert(is_cases_app(fn));
        lean_assert(is_eqp(find(get_app_fn(e)), fn));
        // TODO(Leo)
        return e;
    }

    static bool is_lc_cast_app(expr const & e) {
        return is_app_of(e, get_lc_cast_name(), 3);
    }

    expr reduce_lc_cast(expr const & e) {
        buffer<expr> args;
        expr const & cast_fn1 = get_app_args(e, args);
        lean_assert(args.size() == 3);
        if (type_checker(m_st, m_lctx).is_def_eq(args[0], args[1])) {
            /* (lc_cast A A t) ==> t */
            return args[2];
        }
        expr major = find(args[2]);
        if (is_lc_cast_app(major)) {
            /* Cast transitivity:
               (lc_cast B C (lc_cast A B t)) ==> (lc_cast A C t)


               lc_cast.{u_1 u_2} : Π {α : Sort u_2} {β : Sort u_1}, α → β */
            buffer<expr> nested_args;
            expr const & cast_fn2 = get_app_args(major, nested_args);
            expr const & C = args[1];
            expr const & A = nested_args[0];
            level u1       = head(const_levels(cast_fn1));
            level u2       = head(tail(const_levels(cast_fn2)));
            return reduce_lc_cast(mk_app(mk_constant(get_lc_cast_name(), {u1, u2}), A, C, nested_args[2]));
        }
        return e;
    }

    expr visit_app(expr const & e) {
        if (is_cases_app(e)) {
            return visit_cases(e);
        } else if (is_lc_cast_app(e)) {
            return reduce_lc_cast(e);
        }
        expr fn = find(get_app_fn(e));
        if (is_lambda(fn)) {
            return beta_reduce(fn, e);
        } else if (is_cases_app(fn)) {
            return distrib_app_cases(fn, e);
        }
        return e;
    }

    expr visit(expr const & e) {
        switch (e.kind()) {
        case expr_kind::Lambda: return visit_lambda(e);
        case expr_kind::Let:    return visit_let(e);
        case expr_kind::Proj:   return visit_proj(e);
        case expr_kind::App:    return visit_app(e);
        default:                return e;
        }
    }

public:
    csimp_fn(environment const & env, local_ctx const & lctx):
        m_st(env), m_lctx(lctx), m_x("_x") {}

    expr operator()(expr const & e) {
        expr r = visit(e);
        return m_lctx.mk_lambda(m_fvars, r);
    }
};
expr csimp(environment const & env, local_ctx const & lctx, expr const & e) {
    return csimp_fn(env, lctx)(e);
}
}
