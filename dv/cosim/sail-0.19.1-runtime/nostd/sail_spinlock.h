/*
 * Copyright 2018 The Hafnium Authors.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#ifndef __SAIL_SPINLOCK__
#define __SAIL_SPINLOCK__

#include <stdatomic.h>

struct sail_spinlock {
	atomic_flag v;
};

#define SPINLOCK_INIT                 \
	{                             \
		.v = ATOMIC_FLAG_INIT \
	}

static inline void sail_spin_init(struct sail_spinlock *l)
{
        *l = (struct sail_spinlock)SPINLOCK_INIT;
}

static inline void sail_spin_lock(struct sail_spinlock *l)
{
	while (atomic_flag_test_and_set_explicit(&l->v, memory_order_acquire)) {
		/* do nothing */
	}
}

static inline void sail_spin_unlock(struct sail_spinlock *l)
{
	atomic_flag_clear_explicit(&l->v, memory_order_release);
}

#endif
