/*
 * Copyright 2020 ETH Zurich
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 */

void matmulNxN(float* matA, float* matB , float* matC, const int N)
{
  float tot;
  for (int i = 0; i < N; ++i) {
    for (int j = 0; j < N; ++j) {
      tot = 0;
      for (int k = 0; k < N; ++k) {
        tot = tot + matA[i*N+k] * matB[k*N+j];
      }
      matC[i*N+j] = tot;
    }
  }
}
