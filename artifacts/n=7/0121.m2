                                                                                                              2   2   2   2   2   2   2
HashTable{AOTideal => ideal (y y  - y y  + y y , y y  - y y  + y y , y y  - y y  - y y , y y  - y y  - y y , y , y , y , y , y , y , y )}
                              4 5    4 6    5 6   2 3    2 6    3 6   1 3    1 5    3 5   1 2    1 4    2 4   1   2   3   4   5   6   7
                                2   2   2         2   2               2         2
          AOTinIdeal => ideal (y , y , y , y y , y , y , y y , y y , y , y y , y )
                                7   6   5   4 5   4   3   2 3   1 3   2   1 2   1
          graph => {set {0, 4}, set {4, 5}, set {4, 6}, set {0, 5}, set {0, 6}, set {5, 6}, set {1, 6}}
                                 2      3     4
          hSeries => 1 + 7T + 17T  + 17T  + 6T
          hyperplanes => {a - e, e - f, e - g, a - f, a - g, f - g, b - g}
          numVariables => 7
          WLPfull => "The AOT algebra has WLP"
          WLPin => "A does not have WLP at A_2"


R = QQ[y_1..y_7]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_4*y_5-y_4*y_6+y_5*y_6, y_2*y_3-y_2*y_6+y_3*y_6, y_1*y_3-y_1*y_5-y_3*y_5, y_1*y_2-y_1*y_4-y_2*y_4, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_7^2, y_6^2, y_5^2, y_4*y_5, y_4^2, y_3^2, y_2*y_3, y_1*y_3, y_2^2, y_1*y_2, y_1^2}})
G = graph {set {0, 4}, set {4, 5}, set {4, 6}, set {0, 5}, set {0, 6}, set {5, 6}, set {1, 6}}
