cmake_minimum_required(VERSION 3.5)
project(strippedXX)

include_directories(/usr/local/include/coin-or/asl /home/David/Ipopt/build/include/coin/ThirdParty)
find_library(COINASL NAMES asl coinasl HINTS /usr/local/lib /home/David/Ipopt/build/lib)
set(SRC_FILES ${PROJECT_SOURCE_DIR}/stripped.c
        ${PROJECT_SOURCE_DIR}/../csr_driver.c
        ${PROJECT_SOURCE_DIR}/../find_inequalities.c
        ${PROJECT_SOURCE_DIR}/../get_jac_asl_aug.c
        ${PROJECT_SOURCE_DIR}/../get_hess_asl_aug.c
        ${PROJECT_SOURCE_DIR}/../mu_adjust_primal.c
        ${PROJECT_SOURCE_DIR}/../sigma_compute.c
        ${PROJECT_SOURCE_DIR}/../suffix_decl_hand.c)


add_executable(stripped ${SRC_FILES})

target_link_libraries(stripped ${COINASL} gfortran m dl)