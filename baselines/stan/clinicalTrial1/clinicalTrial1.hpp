
// Code generated by stanc v2.28.1
#include <stan/model/model_header.hpp>
namespace clinicalTrial1_model_namespace {

using stan::io::dump;
using stan::model::assign;
using stan::model::index_uni;
using stan::model::index_max;
using stan::model::index_min;
using stan::model::index_min_max;
using stan::model::index_multi;
using stan::model::index_omni;
using stan::model::model_base_crtp;
using stan::model::rvalue;
using namespace stan::math;


stan::math::profile_map profiles__;
static constexpr std::array<const char*, 52> locations_array__ = 
{" (found before start of program)",
 " (in 'benchmarks/clinicalTrial1/clinicalTrial1.stan', line 7, column 2 to column 33)",
 " (in 'benchmarks/clinicalTrial1/clinicalTrial1.stan', line 8, column 2 to column 37)",
 " (in 'benchmarks/clinicalTrial1/clinicalTrial1.stan', line 9, column 2 to column 37)",
 " (in 'benchmarks/clinicalTrial1/clinicalTrial1.stan', line 13, column 2 to column 10)",
 " (in 'benchmarks/clinicalTrial1/clinicalTrial1.stan', line 14, column 2 to column 9)",
 " (in 'benchmarks/clinicalTrial1/clinicalTrial1.stan', line 15, column 4 to column 19)",
 " (in 'benchmarks/clinicalTrial1/clinicalTrial1.stan', line 16, column 4 to column 27)",
 " (in 'benchmarks/clinicalTrial1/clinicalTrial1.stan', line 18, column 6 to column 71)",
 " (in 'benchmarks/clinicalTrial1/clinicalTrial1.stan', line 29, column 10 to column 81)",
 " (in 'benchmarks/clinicalTrial1/clinicalTrial1.stan', line 30, column 10 to column 81)",
 " (in 'benchmarks/clinicalTrial1/clinicalTrial1.stan', line 28, column 23 to line 32, column 9)",
 " (in 'benchmarks/clinicalTrial1/clinicalTrial1.stan', line 28, column 8 to line 32, column 9)",
 " (in 'benchmarks/clinicalTrial1/clinicalTrial1.stan', line 27, column 10 to line 34, column 7)",
 " (in 'benchmarks/clinicalTrial1/clinicalTrial1.stan', line 21, column 10 to column 85)",
 " (in 'benchmarks/clinicalTrial1/clinicalTrial1.stan', line 22, column 10 to column 85)",
 " (in 'benchmarks/clinicalTrial1/clinicalTrial1.stan', line 20, column 23 to line 24, column 9)",
 " (in 'benchmarks/clinicalTrial1/clinicalTrial1.stan', line 20, column 8 to line 24, column 9)",
 " (in 'benchmarks/clinicalTrial1/clinicalTrial1.stan', line 19, column 31 to line 26, column 7)",
 " (in 'benchmarks/clinicalTrial1/clinicalTrial1.stan', line 19, column 6 to line 34, column 7)",
 " (in 'benchmarks/clinicalTrial1/clinicalTrial1.stan', line 17, column 33 to line 35, column 5)",
 " (in 'benchmarks/clinicalTrial1/clinicalTrial1.stan', line 17, column 4 to line 35, column 5)",
 " (in 'benchmarks/clinicalTrial1/clinicalTrial1.stan', line 36, column 4 to column 28)",
 " (in 'benchmarks/clinicalTrial1/clinicalTrial1.stan', line 15, column 2 to line 37, column 3)",
 " (in 'benchmarks/clinicalTrial1/clinicalTrial1.stan', line 48, column 2 to column 18)",
 " (in 'benchmarks/clinicalTrial1/clinicalTrial1.stan', line 49, column 4 to column 19)",
 " (in 'benchmarks/clinicalTrial1/clinicalTrial1.stan', line 50, column 4 to column 27)",
 " (in 'benchmarks/clinicalTrial1/clinicalTrial1.stan', line 52, column 6 to column 71)",
 " (in 'benchmarks/clinicalTrial1/clinicalTrial1.stan', line 63, column 10 to column 81)",
 " (in 'benchmarks/clinicalTrial1/clinicalTrial1.stan', line 64, column 10 to column 81)",
 " (in 'benchmarks/clinicalTrial1/clinicalTrial1.stan', line 62, column 23 to line 66, column 9)",
 " (in 'benchmarks/clinicalTrial1/clinicalTrial1.stan', line 62, column 8 to line 66, column 9)",
 " (in 'benchmarks/clinicalTrial1/clinicalTrial1.stan', line 61, column 10 to line 68, column 7)",
 " (in 'benchmarks/clinicalTrial1/clinicalTrial1.stan', line 55, column 10 to column 85)",
 " (in 'benchmarks/clinicalTrial1/clinicalTrial1.stan', line 56, column 10 to column 85)",
 " (in 'benchmarks/clinicalTrial1/clinicalTrial1.stan', line 54, column 23 to line 58, column 9)",
 " (in 'benchmarks/clinicalTrial1/clinicalTrial1.stan', line 54, column 8 to line 58, column 9)",
 " (in 'benchmarks/clinicalTrial1/clinicalTrial1.stan', line 53, column 31 to line 60, column 7)",
 " (in 'benchmarks/clinicalTrial1/clinicalTrial1.stan', line 53, column 6 to line 68, column 7)",
 " (in 'benchmarks/clinicalTrial1/clinicalTrial1.stan', line 51, column 33 to line 69, column 5)",
 " (in 'benchmarks/clinicalTrial1/clinicalTrial1.stan', line 51, column 4 to line 69, column 5)",
 " (in 'benchmarks/clinicalTrial1/clinicalTrial1.stan', line 70, column 4 to column 46)",
 " (in 'benchmarks/clinicalTrial1/clinicalTrial1.stan', line 49, column 2 to line 71, column 3)",
 " (in 'benchmarks/clinicalTrial1/clinicalTrial1.stan', line 41, column 2 to column 30)",
 " (in 'benchmarks/clinicalTrial1/clinicalTrial1.stan', line 42, column 2 to column 30)",
 " (in 'benchmarks/clinicalTrial1/clinicalTrial1.stan', line 43, column 2 to column 26)",
 " (in 'benchmarks/clinicalTrial1/clinicalTrial1.stan', line 44, column 2 to column 15)",
 " (in 'benchmarks/clinicalTrial1/clinicalTrial1.stan', line 2, column 2 to column 8)",
 " (in 'benchmarks/clinicalTrial1/clinicalTrial1.stan', line 3, column 23 to column 24)",
 " (in 'benchmarks/clinicalTrial1/clinicalTrial1.stan', line 3, column 2 to column 26)",
 " (in 'benchmarks/clinicalTrial1/clinicalTrial1.stan', line 4, column 23 to column 24)",
 " (in 'benchmarks/clinicalTrial1/clinicalTrial1.stan', line 4, column 2 to column 26)"};



class clinicalTrial1_model final : public model_base_crtp<clinicalTrial1_model> {

 private:
  int N;
  std::vector<int> controlGroupFlip;
  std::vector<int> treatedGroupFlip; 
  
 
 public:
  ~clinicalTrial1_model() { }
  
  inline std::string model_name() const final { return "clinicalTrial1_model"; }

  inline std::vector<std::string> model_compile_info() const noexcept {
    return std::vector<std::string>{"stanc_version = stanc3 v2.28.1", "stancflags = "};
  }
  
  
  clinicalTrial1_model(stan::io::var_context& context__,
                       unsigned int random_seed__ = 0,
                       std::ostream* pstream__ = nullptr) : model_base_crtp(0) {
    int current_statement__ = 0;
    using local_scalar_t__ = double ;
    boost::ecuyer1988 base_rng__ = 
        stan::services::util::create_rng(random_seed__, 0);
    (void) base_rng__;  // suppress unused var warning
    static constexpr const char* function__ = "clinicalTrial1_model_namespace::clinicalTrial1_model";
    (void) function__;  // suppress unused var warning
    local_scalar_t__ DUMMY_VAR__(std::numeric_limits<double>::quiet_NaN());
    (void) DUMMY_VAR__;  // suppress unused var warning
    try {
      int pos__;
      pos__ = std::numeric_limits<int>::min();
      
      pos__ = 1;
      current_statement__ = 47;
      context__.validate_dims("data initialization","N","int",
           std::vector<size_t>{});
      N = std::numeric_limits<int>::min();
      
      current_statement__ = 47;
      N = context__.vals_i("N")[(1 - 1)];
      current_statement__ = 48;
      validate_non_negative_index("controlGroupFlip", "N", N);
      current_statement__ = 49;
      context__.validate_dims("data initialization","controlGroupFlip","int",
           std::vector<size_t>{static_cast<size_t>(N)});
      controlGroupFlip = std::vector<int>(N, std::numeric_limits<int>::min());
      
      current_statement__ = 49;
      controlGroupFlip = context__.vals_i("controlGroupFlip");
      current_statement__ = 50;
      validate_non_negative_index("treatedGroupFlip", "N", N);
      current_statement__ = 51;
      context__.validate_dims("data initialization","treatedGroupFlip","int",
           std::vector<size_t>{static_cast<size_t>(N)});
      treatedGroupFlip = std::vector<int>(N, std::numeric_limits<int>::min());
      
      current_statement__ = 51;
      treatedGroupFlip = context__.vals_i("treatedGroupFlip");
    } catch (const std::exception& e) {
      stan::lang::rethrow_located(e, locations_array__[current_statement__]);
    }
    num_params_r__ = 1 + 1 + 1;
    
  }
  
  template <bool propto__, bool jacobian__ , typename VecR, typename VecI, 
  stan::require_vector_like_t<VecR>* = nullptr, 
  stan::require_vector_like_vt<std::is_integral, VecI>* = nullptr> 
  inline stan::scalar_type_t<VecR> log_prob_impl(VecR& params_r__,
                                                 VecI& params_i__,
                                                 std::ostream* pstream__ = nullptr) const {
    using T__ = stan::scalar_type_t<VecR>;
    using local_scalar_t__ = T__;
    T__ lp__(0.0);
    stan::math::accumulator<T__> lp_accum__;
    stan::io::deserializer<local_scalar_t__> in__(params_r__, params_i__);
    int current_statement__ = 0;
    local_scalar_t__ DUMMY_VAR__(std::numeric_limits<double>::quiet_NaN());
    (void) DUMMY_VAR__;  // suppress unused var warning
    static constexpr const char* function__ = "clinicalTrial1_model_namespace::log_prob";
    (void) function__;  // suppress unused var warning
    
    try {
      local_scalar_t__ probAll;
      probAll = DUMMY_VAR__;
      
      current_statement__ = 1;
      probAll = in__.template read_constrain_lub<local_scalar_t__, jacobian__>(
                  0, 1, lp__);
      local_scalar_t__ probControl;
      probControl = DUMMY_VAR__;
      
      current_statement__ = 2;
      probControl = in__.template read_constrain_lub<local_scalar_t__, jacobian__>(
                      0, 1, lp__);
      local_scalar_t__ probTreated;
      probTreated = DUMMY_VAR__;
      
      current_statement__ = 3;
      probTreated = in__.template read_constrain_lub<local_scalar_t__, jacobian__>(
                      0, 1, lp__);
      local_scalar_t__ m1;
      m1 = DUMMY_VAR__;
      
      current_statement__ = 5;
      m1 = 0;
      {
        Eigen::Matrix<local_scalar_t__, -1, 1> acc0;
        acc0 = Eigen::Matrix<local_scalar_t__, -1, 1>(2);
        stan::math::fill(acc0, DUMMY_VAR__);
        
        current_statement__ = 7;
        assign(acc0, rep_vector(0, 2), "assigning variable acc0");
        current_statement__ = 21;
        for (int isEffective_val = 1; isEffective_val <= 2; ++isEffective_val) {
          current_statement__ = 8;
          assign(acc0,
            (rvalue(acc0, "acc0", index_uni(isEffective_val)) +
              bernoulli_lpmf<false>((isEffective_val - 1), 0.5)),
            "assigning variable acc0", index_uni(isEffective_val));
          current_statement__ = 19;
          if (logical_gt(isEffective_val, 1)) {
            current_statement__ = 17;
            for (int n = 1; n <= N; ++n) {
              current_statement__ = 14;
              assign(acc0,
                (rvalue(acc0, "acc0", index_uni(isEffective_val)) +
                  bernoulli_lpmf<false>(
                    rvalue(controlGroupFlip, "controlGroupFlip",
                      index_uni(n)), probControl)),
                "assigning variable acc0", index_uni(isEffective_val));
              current_statement__ = 15;
              assign(acc0,
                (rvalue(acc0, "acc0", index_uni(isEffective_val)) +
                  bernoulli_lpmf<false>(
                    rvalue(treatedGroupFlip, "treatedGroupFlip",
                      index_uni(n)), probTreated)),
                "assigning variable acc0", index_uni(isEffective_val));
            }
          } else {
            current_statement__ = 12;
            for (int n = 1; n <= N; ++n) {
              current_statement__ = 9;
              assign(acc0,
                (rvalue(acc0, "acc0", index_uni(isEffective_val)) +
                  bernoulli_lpmf<false>(
                    rvalue(controlGroupFlip, "controlGroupFlip",
                      index_uni(n)), probAll)),
                "assigning variable acc0", index_uni(isEffective_val));
              current_statement__ = 10;
              assign(acc0,
                (rvalue(acc0, "acc0", index_uni(isEffective_val)) +
                  bernoulli_lpmf<false>(
                    rvalue(treatedGroupFlip, "treatedGroupFlip",
                      index_uni(n)), probAll)),
                "assigning variable acc0", index_uni(isEffective_val));
            }
          }
        }
        current_statement__ = 22;
        m1 = (m1 + log_sum_exp(acc0));
      }
      {
        current_statement__ = 43;
        lp_accum__.add(uniform_lpdf<propto__>(probControl, 0, 1));
        current_statement__ = 44;
        lp_accum__.add(uniform_lpdf<propto__>(probTreated, 0, 1));
        current_statement__ = 45;
        lp_accum__.add(uniform_lpdf<propto__>(probAll, 0, 1));
        current_statement__ = 46;
        lp_accum__.add(m1);
      }
    } catch (const std::exception& e) {
      stan::lang::rethrow_located(e, locations_array__[current_statement__]);
    }
    lp_accum__.add(lp__);
    return lp_accum__.sum();
    } // log_prob_impl() 
    
  template <typename RNG, typename VecR, typename VecI, typename VecVar, 
  stan::require_vector_like_vt<std::is_floating_point, VecR>* = nullptr, 
  stan::require_vector_like_vt<std::is_integral, VecI>* = nullptr, 
  stan::require_std_vector_vt<std::is_floating_point, VecVar>* = nullptr> 
  inline void write_array_impl(RNG& base_rng__, VecR& params_r__,
                               VecI& params_i__, VecVar& vars__,
                               const bool emit_transformed_parameters__ = true,
                               const bool emit_generated_quantities__ = true,
                               std::ostream* pstream__ = nullptr) const {
    using local_scalar_t__ = double;
    stan::io::deserializer<local_scalar_t__> in__(params_r__, params_i__);
    stan::io::serializer<local_scalar_t__> out__(vars__);
    static constexpr bool propto__ = true;
    (void) propto__;
    double lp__ = 0.0;
    (void) lp__;  // dummy to suppress unused var warning
    int current_statement__ = 0; 
    stan::math::accumulator<double> lp_accum__;
    local_scalar_t__ DUMMY_VAR__(std::numeric_limits<double>::quiet_NaN());
    constexpr bool jacobian__ = false;
    (void) DUMMY_VAR__;  // suppress unused var warning
    static constexpr const char* function__ = "clinicalTrial1_model_namespace::write_array";
    (void) function__;  // suppress unused var warning
    
    try {
      double probAll;
      probAll = std::numeric_limits<double>::quiet_NaN();
      
      current_statement__ = 1;
      probAll = in__.template read_constrain_lub<local_scalar_t__, jacobian__>(
                  0, 1, lp__);
      double probControl;
      probControl = std::numeric_limits<double>::quiet_NaN();
      
      current_statement__ = 2;
      probControl = in__.template read_constrain_lub<local_scalar_t__, jacobian__>(
                      0, 1, lp__);
      double probTreated;
      probTreated = std::numeric_limits<double>::quiet_NaN();
      
      current_statement__ = 3;
      probTreated = in__.template read_constrain_lub<local_scalar_t__, jacobian__>(
                      0, 1, lp__);
      double m1;
      m1 = std::numeric_limits<double>::quiet_NaN();
      
      out__.write(probAll);
      out__.write(probControl);
      out__.write(probTreated);
      if (logical_negation((primitive_value(emit_transformed_parameters__) ||
            primitive_value(emit_generated_quantities__)))) {
        return ;
      } 
      current_statement__ = 5;
      m1 = 0;
      {
        Eigen::Matrix<double, -1, 1> acc0;
        acc0 = Eigen::Matrix<double, -1, 1>(2);
        stan::math::fill(acc0, std::numeric_limits<double>::quiet_NaN());
        
        current_statement__ = 7;
        assign(acc0, rep_vector(0, 2), "assigning variable acc0");
        current_statement__ = 21;
        for (int isEffective_val = 1; isEffective_val <= 2; ++isEffective_val) {
          current_statement__ = 8;
          assign(acc0,
            (rvalue(acc0, "acc0", index_uni(isEffective_val)) +
              bernoulli_lpmf<false>((isEffective_val - 1), 0.5)),
            "assigning variable acc0", index_uni(isEffective_val));
          current_statement__ = 19;
          if (logical_gt(isEffective_val, 1)) {
            current_statement__ = 17;
            for (int n = 1; n <= N; ++n) {
              current_statement__ = 14;
              assign(acc0,
                (rvalue(acc0, "acc0", index_uni(isEffective_val)) +
                  bernoulli_lpmf<false>(
                    rvalue(controlGroupFlip, "controlGroupFlip",
                      index_uni(n)), probControl)),
                "assigning variable acc0", index_uni(isEffective_val));
              current_statement__ = 15;
              assign(acc0,
                (rvalue(acc0, "acc0", index_uni(isEffective_val)) +
                  bernoulli_lpmf<false>(
                    rvalue(treatedGroupFlip, "treatedGroupFlip",
                      index_uni(n)), probTreated)),
                "assigning variable acc0", index_uni(isEffective_val));
            }
          } else {
            current_statement__ = 12;
            for (int n = 1; n <= N; ++n) {
              current_statement__ = 9;
              assign(acc0,
                (rvalue(acc0, "acc0", index_uni(isEffective_val)) +
                  bernoulli_lpmf<false>(
                    rvalue(controlGroupFlip, "controlGroupFlip",
                      index_uni(n)), probAll)),
                "assigning variable acc0", index_uni(isEffective_val));
              current_statement__ = 10;
              assign(acc0,
                (rvalue(acc0, "acc0", index_uni(isEffective_val)) +
                  bernoulli_lpmf<false>(
                    rvalue(treatedGroupFlip, "treatedGroupFlip",
                      index_uni(n)), probAll)),
                "assigning variable acc0", index_uni(isEffective_val));
            }
          }
        }
        current_statement__ = 22;
        m1 = (m1 + log_sum_exp(acc0));
      }
      if (emit_transformed_parameters__) {
        out__.write(m1);
      } 
      if (logical_negation(emit_generated_quantities__)) {
        return ;
      } 
      int isEffective;
      isEffective = std::numeric_limits<int>::min();
      
      {
        Eigen::Matrix<double, -1, 1> acc0;
        acc0 = Eigen::Matrix<double, -1, 1>(2);
        stan::math::fill(acc0, std::numeric_limits<double>::quiet_NaN());
        
        current_statement__ = 26;
        assign(acc0, rep_vector(0, 2), "assigning variable acc0");
        current_statement__ = 40;
        for (int isEffective_val = 1; isEffective_val <= 2; ++isEffective_val) {
          current_statement__ = 27;
          assign(acc0,
            (rvalue(acc0, "acc0", index_uni(isEffective_val)) +
              bernoulli_lpmf<false>((isEffective_val - 1), 0.5)),
            "assigning variable acc0", index_uni(isEffective_val));
          current_statement__ = 38;
          if (logical_gt(isEffective_val, 1)) {
            current_statement__ = 36;
            for (int n = 1; n <= N; ++n) {
              current_statement__ = 33;
              assign(acc0,
                (rvalue(acc0, "acc0", index_uni(isEffective_val)) +
                  bernoulli_lpmf<false>(
                    rvalue(controlGroupFlip, "controlGroupFlip",
                      index_uni(n)), probControl)),
                "assigning variable acc0", index_uni(isEffective_val));
              current_statement__ = 34;
              assign(acc0,
                (rvalue(acc0, "acc0", index_uni(isEffective_val)) +
                  bernoulli_lpmf<false>(
                    rvalue(treatedGroupFlip, "treatedGroupFlip",
                      index_uni(n)), probTreated)),
                "assigning variable acc0", index_uni(isEffective_val));
            }
          } else {
            current_statement__ = 31;
            for (int n = 1; n <= N; ++n) {
              current_statement__ = 28;
              assign(acc0,
                (rvalue(acc0, "acc0", index_uni(isEffective_val)) +
                  bernoulli_lpmf<false>(
                    rvalue(controlGroupFlip, "controlGroupFlip",
                      index_uni(n)), probAll)),
                "assigning variable acc0", index_uni(isEffective_val));
              current_statement__ = 29;
              assign(acc0,
                (rvalue(acc0, "acc0", index_uni(isEffective_val)) +
                  bernoulli_lpmf<false>(
                    rvalue(treatedGroupFlip, "treatedGroupFlip",
                      index_uni(n)), probAll)),
                "assigning variable acc0", index_uni(isEffective_val));
            }
          }
        }
        current_statement__ = 41;
        isEffective = categorical_logit_rng(acc0, base_rng__);
      }
      out__.write(isEffective);
    } catch (const std::exception& e) {
      stan::lang::rethrow_located(e, locations_array__[current_statement__]);
    }
    } // write_array_impl() 
    
  template <typename VecVar, typename VecI, 
  stan::require_std_vector_t<VecVar>* = nullptr, 
  stan::require_vector_like_vt<std::is_integral, VecI>* = nullptr> 
  inline void transform_inits_impl(VecVar& params_r__, VecI& params_i__,
                                   VecVar& vars__,
                                   std::ostream* pstream__ = nullptr) const {
    using local_scalar_t__ = double;
    stan::io::deserializer<local_scalar_t__> in__(params_r__, params_i__);
    stan::io::serializer<local_scalar_t__> out__(vars__);
    int current_statement__ = 0;
    local_scalar_t__ DUMMY_VAR__(std::numeric_limits<double>::quiet_NaN());
    
    try {
      int pos__;
      pos__ = std::numeric_limits<int>::min();
      
      pos__ = 1;
      local_scalar_t__ probAll;
      probAll = DUMMY_VAR__;
      
      probAll = in__.read<local_scalar_t__>();
      out__.write_free_lub(0, 1, probAll);
      local_scalar_t__ probControl;
      probControl = DUMMY_VAR__;
      
      probControl = in__.read<local_scalar_t__>();
      out__.write_free_lub(0, 1, probControl);
      local_scalar_t__ probTreated;
      probTreated = DUMMY_VAR__;
      
      probTreated = in__.read<local_scalar_t__>();
      out__.write_free_lub(0, 1, probTreated);
    } catch (const std::exception& e) {
      stan::lang::rethrow_located(e, locations_array__[current_statement__]);
    }
    } // transform_inits_impl() 
    
  inline void get_param_names(std::vector<std::string>& names__) const {
    
    names__ = std::vector<std::string>{"probAll", "probControl",
      "probTreated", "m1", "isEffective"};
    
    } // get_param_names() 
    
  inline void get_dims(std::vector<std::vector<size_t>>& dimss__) const {
    
    dimss__ = std::vector<std::vector<size_t>>{std::vector<size_t>{},
      std::vector<size_t>{}, std::vector<size_t>{}, std::vector<size_t>{
      }, std::vector<size_t>{}};
    
    } // get_dims() 
    
  inline void constrained_param_names(
                                      std::vector<std::string>& param_names__,
                                      bool emit_transformed_parameters__ = true,
                                      bool emit_generated_quantities__ = true) const
    final {
    
    param_names__.emplace_back(std::string() + "probAll");
    param_names__.emplace_back(std::string() + "probControl");
    param_names__.emplace_back(std::string() + "probTreated");
    if (emit_transformed_parameters__) {
      param_names__.emplace_back(std::string() + "m1");
    }
    
    if (emit_generated_quantities__) {
      param_names__.emplace_back(std::string() + "isEffective");
    }
    
    } // constrained_param_names() 
    
  inline void unconstrained_param_names(
                                        std::vector<std::string>& param_names__,
                                        bool emit_transformed_parameters__ = true,
                                        bool emit_generated_quantities__ = true) const
    final {
    
    param_names__.emplace_back(std::string() + "probAll");
    param_names__.emplace_back(std::string() + "probControl");
    param_names__.emplace_back(std::string() + "probTreated");
    if (emit_transformed_parameters__) {
      param_names__.emplace_back(std::string() + "m1");
    }
    
    if (emit_generated_quantities__) {
      param_names__.emplace_back(std::string() + "isEffective");
    }
    
    } // unconstrained_param_names() 
    
  inline std::string get_constrained_sizedtypes() const {
    
    return std::string("[{\"name\":\"probAll\",\"type\":{\"name\":\"real\"},\"block\":\"parameters\"},{\"name\":\"probControl\",\"type\":{\"name\":\"real\"},\"block\":\"parameters\"},{\"name\":\"probTreated\",\"type\":{\"name\":\"real\"},\"block\":\"parameters\"},{\"name\":\"m1\",\"type\":{\"name\":\"real\"},\"block\":\"transformed_parameters\"},{\"name\":\"isEffective\",\"type\":{\"name\":\"int\"},\"block\":\"generated_quantities\"}]");
    
    } // get_constrained_sizedtypes() 
    
  inline std::string get_unconstrained_sizedtypes() const {
    
    return std::string("[{\"name\":\"probAll\",\"type\":{\"name\":\"real\"},\"block\":\"parameters\"},{\"name\":\"probControl\",\"type\":{\"name\":\"real\"},\"block\":\"parameters\"},{\"name\":\"probTreated\",\"type\":{\"name\":\"real\"},\"block\":\"parameters\"},{\"name\":\"m1\",\"type\":{\"name\":\"real\"},\"block\":\"transformed_parameters\"},{\"name\":\"isEffective\",\"type\":{\"name\":\"int\"},\"block\":\"generated_quantities\"}]");
    
    } // get_unconstrained_sizedtypes() 
    
  
    // Begin method overload boilerplate
    template <typename RNG>
    inline void write_array(RNG& base_rng,
                            Eigen::Matrix<double,Eigen::Dynamic,1>& params_r,
                            Eigen::Matrix<double,Eigen::Dynamic,1>& vars,
                            const bool emit_transformed_parameters = true,
                            const bool emit_generated_quantities = true,
                            std::ostream* pstream = nullptr) const {
      const size_t num_params__ = 
  ((1 + 1) + 1);
      const size_t num_transformed = 1;
      const size_t num_gen_quantities = 1;
      std::vector<double> vars_vec(num_params__
       + (emit_transformed_parameters * num_transformed)
       + (emit_generated_quantities * num_gen_quantities));
      std::vector<int> params_i;
      write_array_impl(base_rng, params_r, params_i, vars_vec,
          emit_transformed_parameters, emit_generated_quantities, pstream);
      vars = Eigen::Map<Eigen::Matrix<double,Eigen::Dynamic,1>>(
        vars_vec.data(), vars_vec.size());
    }

    template <typename RNG>
    inline void write_array(RNG& base_rng, std::vector<double>& params_r,
                            std::vector<int>& params_i,
                            std::vector<double>& vars,
                            bool emit_transformed_parameters = true,
                            bool emit_generated_quantities = true,
                            std::ostream* pstream = nullptr) const {
      const size_t num_params__ = 
  ((1 + 1) + 1);
      const size_t num_transformed = 1;
      const size_t num_gen_quantities = 1;
      vars.resize(num_params__
        + (emit_transformed_parameters * num_transformed)
        + (emit_generated_quantities * num_gen_quantities));
      write_array_impl(base_rng, params_r, params_i, vars, emit_transformed_parameters, emit_generated_quantities, pstream);
    }

    template <bool propto__, bool jacobian__, typename T_>
    inline T_ log_prob(Eigen::Matrix<T_,Eigen::Dynamic,1>& params_r,
                       std::ostream* pstream = nullptr) const {
      Eigen::Matrix<int, -1, 1> params_i;
      return log_prob_impl<propto__, jacobian__>(params_r, params_i, pstream);
    }

    template <bool propto__, bool jacobian__, typename T__>
    inline T__ log_prob(std::vector<T__>& params_r,
                        std::vector<int>& params_i,
                        std::ostream* pstream = nullptr) const {
      return log_prob_impl<propto__, jacobian__>(params_r, params_i, pstream);
    }


    inline void transform_inits(const stan::io::var_context& context,
                         Eigen::Matrix<double, Eigen::Dynamic, 1>& params_r,
                         std::ostream* pstream = nullptr) const final {
      std::vector<double> params_r_vec(params_r.size());
      std::vector<int> params_i;
      transform_inits(context, params_i, params_r_vec, pstream);
      params_r = Eigen::Map<Eigen::Matrix<double,Eigen::Dynamic,1>>(
        params_r_vec.data(), params_r_vec.size());
    }

  inline void transform_inits(const stan::io::var_context& context,
                              std::vector<int>& params_i,
                              std::vector<double>& vars,
                              std::ostream* pstream__ = nullptr) const {
     constexpr std::array<const char*, 3> names__{"probAll", "probControl",
      "probTreated"};
      const std::array<Eigen::Index, 3> constrain_param_sizes__{1, 1, 1};
      const auto num_constrained_params__ = std::accumulate(
        constrain_param_sizes__.begin(), constrain_param_sizes__.end(), 0);
    
     std::vector<double> params_r_flat__(num_constrained_params__);
     Eigen::Index size_iter__ = 0;
     Eigen::Index flat_iter__ = 0;
     for (auto&& param_name__ : names__) {
       const auto param_vec__ = context.vals_r(param_name__);
       for (Eigen::Index i = 0; i < constrain_param_sizes__[size_iter__]; ++i) {
         params_r_flat__[flat_iter__] = param_vec__[i];
         ++flat_iter__;
       }
       ++size_iter__;
     }
     vars.resize(num_params_r__);
     transform_inits_impl(params_r_flat__, params_i, vars, pstream__);
    } // transform_inits() 
    
};
}
using stan_model = clinicalTrial1_model_namespace::clinicalTrial1_model;

#ifndef USING_R

// Boilerplate
stan::model::model_base& new_model(
        stan::io::var_context& data_context,
        unsigned int seed,
        std::ostream* msg_stream) {
  stan_model* m = new stan_model(data_context, seed, msg_stream);
  return *m;
}

stan::math::profile_map& get_stan_profile_data() {
  return clinicalTrial1_model_namespace::profiles__;
}

#endif


