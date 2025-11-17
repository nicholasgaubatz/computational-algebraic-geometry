                                                  2   2   2
HashTable{AOTideal => ideal (y y  - y y  - y y , y , y , y )}
                              1 2    1 3    2 3   1   2   3
                                2   2         2
          AOTinIdeal => ideal (y , y , y y , y )
                                3   2   1 2   1
          graph => {set {0, 4}, set {4, 5}, set {0, 5}}
                                2
          hSeries => 1 + 3T + 2T
          hyperplanes => {a - e, e - f, a - f}
          numVariables => 3
          WLPfull => "The AOT algebra has WLP"
          WLPin => "The AOT algebra has WLP"


R = QQ[y_1..y_3]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}},{{y_1*y_2-y_1*y_3-y_2*y_3, y_1^2, y_2^2, y_3^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}},{{y_3^2, y_2^2, y_1*y_2, y_1^2}})
G = graph {set {0, 4}, set {4, 5}, set {0, 5}}
