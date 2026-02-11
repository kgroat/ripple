/** @import {AnalyzeOptions, RippleCompileError} from 'ripple/compiler'  */
/**
@import {
	AnalysisResult,
	AnalysisState,
	AnalysisContext,
	ScopeInterface,
	Visitors,
	TopScopedClasses,
	StyleClasses,
	ControlFlowChecks,
} from '#compiler';
*/
/**
@import * as AST from 'estree';
@import * as ESTreeJSX from 'estree-jsx';
*/

import * as b from '../../../utils/builders.js';
import { walk } from 'zimmerframe';
import { create_scopes, ScopeRoot } from '../../scope.js';
import {
	is_delegated_event,
	get_parent_block_node,
	is_element_dom_element,
	is_inside_component,
	is_ripple_track_call,
	is_void_element,
	normalize_children,
	is_binding_function,
	is_inside_try_block,
} from '../../utils.js';
import { extract_paths } from '../../../utils/ast.js';
import is_reference from 'is-reference';
import { prune_css } from './prune.js';
import { analyze_css } from './css-analyze.js';
import { error } from '../../errors.js';
import { is_event_attribute } from '../../../utils/events.js';
import { validate_nesting } from './validation.js';

const valid_in_head = new Set(['title', 'base', 'link', 'meta', 'style', 'script', 'noscript']);

/** @returns {ControlFlowChecks} */
function create_control_flow_checks() {
	return {
		registry: new Map(),
		results: new Map(),
	};
}

/**
 * @param {ControlFlowChecks} checks
 * @param {AST.Node} owner
 * @param {string[]} requirements
 */
function register_check(checks, owner, requirements) {
	if (!checks) return;
	let owner_checks = checks.registry.get(owner);
	if (!owner_checks) {
		owner_checks = [];
		checks.registry.set(owner, owner_checks);
	}
	owner_checks.push({
		requirements,
		satisfied: false,
	});
}

/**
 * @param {ControlFlowChecks} checks
 * @param {AnalysisContext['path']} path
 * @param {string} type
 */
function satisfy_check(checks, path, type) {
	if (!checks) return;
	for (let i = path.length - 1; i >= 0; i--) {
		const node = path[i];
		if (
			node.type === 'Component' ||
			node.type === 'FunctionExpression' ||
			node.type === 'ArrowFunctionExpression' ||
			node.type === 'FunctionDeclaration'
		) {
			break;
		}

		const owner_checks = checks.registry.get(node);
		if (owner_checks) {
			for (const check of owner_checks) {
				if (!check.satisfied && check.requirements.includes(type)) {
					check.satisfied = true;
				}
			}
		}
	}
}

/**
 * @param {ControlFlowChecks | undefined} checks
 * @param {AST.Node} owner
 * @returns {boolean}
 */
function is_check_satisfied(checks, owner) {
	if (!checks) return true;
	const owner_checks = checks.registry.get(owner);
	if (!owner_checks) return true;
	for (const check of owner_checks) {
		if (check.satisfied) return true;
	}
	return false;
}

/**
 * @param {AST.BlockStatement | AST.Statement} block
 * @param {string} filename
 * @param {RippleCompileError[] | undefined} errors
 */
function check_unreachable_after_return(block, filename, errors) {
	if (block.type !== 'BlockStatement') return;
	const body = /** @type {AST.Node[]} */ (block.body);
	let found_return = false;

	for (const stmt of body) {
		if (found_return && (stmt.type === 'Element' || stmt.type === 'Component')) {
			error('Unreachable template content after return statement', filename, stmt, errors);
		}
		if (found_return && stmt.type === 'IfStatement') {
			const has_template = if_statement_has_template(stmt);
			if (has_template) {
				error('Unreachable template content after return statement', filename, stmt, errors);
			}
		}
		if (stmt.type === 'ReturnStatement') {
			found_return = true;
		}
	}
}

/**
 * @param {AST.IfStatement} node
 * @returns {boolean}
 */
function if_statement_has_template(node) {
	/**
	 * @param {AST.BlockStatement | AST.Statement} body
	 * @returns {boolean}
	 */
	const check_body = (body) => {
		if (!body || body.type !== 'BlockStatement') return false;
		const stmts = /** @type {AST.Node[]} */ (body.body);
		for (const stmt of stmts) {
			if (stmt.type === 'Element' || stmt.type === 'Component') {
				return true;
			}
			if (stmt.type === 'IfStatement' && if_statement_has_template(stmt)) {
				return true;
			}
		}
		return false;
	};

	if (check_body(node.consequent)) return true;
	if (node.alternate && check_body(node.alternate)) return true;
	return false;
}

/**
 * @param {AnalysisContext['path']} path
 */
function mark_control_flow_has_return(path) {
	for (let i = path.length - 1; i >= 0; i -= 1) {
		const node = path[i];

		if (
			node.type === 'Component' ||
			node.type === 'FunctionExpression' ||
			node.type === 'ArrowFunctionExpression' ||
			node.type === 'FunctionDeclaration'
		) {
			break;
		}
		if (node.type === 'IfStatement' || node.type === 'Element') {
			node.metadata.has_return = true;
		}
	}
}

/**
 * @param {AST.Function} node
 * @param {AnalysisContext} context
 */
function visit_function(node, context) {
	node.metadata = {
		tracked: false,
		path: [...context.path],
	};

	context.next({
		...context.state,
		function_depth: (context.state.function_depth ?? 0) + 1,
	});

	if (node.metadata.tracked) {
		mark_as_tracked(context.path);
	}
}

/**
 * @param {AnalysisContext['path']} path
 */
function mark_as_tracked(path) {
	for (let i = path.length - 1; i >= 0; i -= 1) {
		const node = path[i];

		if (node.type === 'Component') {
			break;
		}
		if (
			node.type === 'FunctionExpression' ||
			node.type === 'ArrowFunctionExpression' ||
			node.type === 'FunctionDeclaration'
		) {
			node.metadata.tracked = true;
			break;
		}
	}
}

/** @type {Visitors<AST.Node, AnalysisState>} */
const visitors = {
	_(node, { state, next, path }) {
		// Set up metadata.path for each node (needed for CSS pruning)
		if (!node.metadata) {
			node.metadata = { path: [...path] };
		} else {
			node.metadata.path = [...path];
		}

		const scope = state.scopes.get(node);
		next(scope !== undefined && scope !== state.scope ? { ...state, scope } : state);
	},

	Program(_, context) {
		return context.next({ ...context.state, function_depth: 0 });
	},

	ServerBlock(node, context) {
		node.metadata = {
			...node.metadata,
			exports: new Set(),
		};
		context.visit(node.body, {
			...context.state,
			ancestor_server_block: node,
		});
	},

	Identifier(node, context) {
		const binding = context.state.scope.get(node.name);
		const parent = context.path.at(-1);

		if (
			is_reference(node, /** @type {AST.Node} */ (parent)) &&
			binding &&
			context.state.ancestor_server_block &&
			binding.node !== node // Don't check the declaration itself
		) {
			/** @type {ScopeInterface | null} */
			let current_scope = binding.scope;
			let found_server_block = false;

			while (current_scope !== null) {
				if (current_scope.server_block) {
					found_server_block = true;
					break;
				}
				current_scope = current_scope.parent;
			}

			if (!found_server_block) {
				error(
					`Cannot reference client-side "${node.name}" from a server block. Server blocks can only access variables and imports declared inside them.`,
					context.state.analysis.module.filename,
					node,
					context.state.loose ? context.state.analysis.errors : undefined,
				);
			}
		}

		if (
			binding?.kind === 'prop' ||
			binding?.kind === 'prop_fallback' ||
			binding?.kind === 'for_pattern'
		) {
			mark_as_tracked(context.path);
			if (context.state.metadata?.tracking === false) {
				context.state.metadata.tracking = true;
			}
		}

		if (
			is_reference(node, /** @type {AST.Node} */ (parent)) &&
			node.tracked &&
			binding?.node !== node
		) {
			mark_as_tracked(context.path);
			if (context.state.metadata?.tracking === false) {
				context.state.metadata.tracking = true;
			}
		}

		if (
			is_reference(node, /** @type {AST.Node} */ (parent)) &&
			node.tracked &&
			binding?.node !== node
		) {
			if (context.state.metadata?.tracking === false) {
				context.state.metadata.tracking = true;
			}
		}

		context.next();
	},

	MemberExpression(node, context) {
		const parent = context.path.at(-1);

		if (context.state.metadata?.tracking === false && parent?.type !== 'AssignmentExpression') {
			context.state.metadata.tracking = true;
		}

		// Track #style.className or #style['className'] references
		if (node.object.type === 'StyleIdentifier') {
			const component = is_inside_component(context, true);

			if (!component) {
				error(
					'`#style` can only be used within a component',
					context.state.analysis.module.filename,
					node,
					context.state.loose ? context.state.analysis.errors : undefined,
				);
			} else {
				component.metadata.styleIdentifierPresent = true;
			}

			/** @type {string | null} */
			let className = null;

			if (!node.computed && node.property.type === 'Identifier') {
				// #style.test
				className = node.property.name;
			} else if (
				node.computed &&
				node.property.type === 'Literal' &&
				typeof node.property.value === 'string'
			) {
				// #style['test']
				className = node.property.value;
			} else {
				// #style[expression] - dynamic, not allowed
				error(
					'`#style` property access must use a dot property or static string for css class name, not a dynamic expression',
					context.state.analysis.module.filename,
					node.property,
					context.state.loose ? context.state.analysis.errors : undefined,
				);
			}

			if (className !== null) {
				context.state.metadata.styleClasses?.set(className, node.property);
			}

			return context.next();
		} else if (node.object.type === 'ServerIdentifier') {
			context.state.analysis.metadata.serverIdentifierPresent = true;
		}

		if (node.object.type === 'Identifier' && !node.object.tracked) {
			const binding = context.state.scope.get(node.object.name);

			if (binding && binding.metadata?.is_tracked_object) {
				const internalProperties = new Set(['__v', 'a', 'b', 'c', 'f']);

				let propertyName = null;
				if (node.property.type === 'Identifier' && !node.computed) {
					propertyName = node.property.name;
				} else if (node.property.type === 'Literal' && typeof node.property.value === 'string') {
					propertyName = node.property.value;
				}

				if (propertyName && internalProperties.has(propertyName)) {
					error(
						`Directly accessing internal property "${propertyName}" of a tracked object is not allowed. Use \`get(${node.object.name})\` or \`@${node.object.name}\` instead.`,
						context.state.analysis.module.filename,
						node.property,
						context.state.loose ? context.state.analysis.errors : undefined,
					);
				}
			}

			if (
				binding !== null &&
				binding.initial?.type === 'CallExpression' &&
				is_ripple_track_call(binding.initial.callee, context)
			) {
				error(
					`Accessing a tracked object directly is not allowed, use the \`@\` prefix to read the value inside a tracked object - for example \`@${node.object.name}${node.property.type === 'Identifier' ? `.${node.property.name}` : ''}\``,
					context.state.analysis.module.filename,
					node.object,
					context.state.loose ? context.state.analysis.errors : undefined,
				);
			}
		}

		context.next();
	},

	CallExpression(node, context) {
		// bug in our acorn [parser]: it uses typeParameters instead of typeArguments
		// @ts-expect-error
		if (node.typeParameters) {
			// @ts-expect-error
			node.typeArguments = node.typeParameters;
			// @ts-expect-error
			delete node.typeParameters;
		}

		const callee = node.callee;

		if (context.state.function_depth === 0 && is_ripple_track_call(callee, context)) {
			error(
				'`track` can only be used within a reactive context, such as a component, function or class that is used or created from a component',
				context.state.analysis.module.filename,
				node.callee,
				context.state.loose ? context.state.analysis.errors : undefined,
			);
		}

		if (context.state.metadata?.tracking === false) {
			context.state.metadata.tracking = true;
		}

		if (!is_inside_component(context, true)) {
			mark_as_tracked(context.path);
		}

		context.next();
	},

	VariableDeclaration(node, context) {
		const { state, visit } = context;

		for (const declarator of node.declarations) {
			if (is_inside_component(context) && node.kind === 'var') {
				error(
					'`var` declarations are not allowed in components, use let or const instead',
					state.analysis.module.filename,
					declarator.id,
					context.state.loose ? context.state.analysis.errors : undefined,
				);
			}
			const metadata = { tracking: false, await: false };

			if (declarator.id.type === 'Identifier') {
				const binding = state.scope.get(declarator.id.name);
				if (binding && declarator.init && declarator.init.type === 'CallExpression') {
					const callee = declarator.init.callee;
					// Check if it's a call to `track` or `tracked`
					if (
						(callee.type === 'Identifier' &&
							(callee.name === 'track' || callee.name === 'tracked')) ||
						(callee.type === 'MemberExpression' &&
							callee.property.type === 'Identifier' &&
							(callee.property.name === 'track' || callee.property.name === 'tracked'))
					) {
						binding.metadata = { ...binding.metadata, is_tracked_object: true };
					}
				}
				visit(declarator, state);
			} else {
				const paths = extract_paths(declarator.id);

				for (const path of paths) {
					if (path.node.tracked) {
						error(
							'Variables cannot be reactively referenced using @',
							state.analysis.module.filename,
							path.node,
							context.state.loose ? context.state.analysis.errors : undefined,
						);
					}
				}

				visit(declarator, state);
			}

			declarator.metadata = { ...metadata, path: [...context.path] };
		}
	},

	ArrowFunctionExpression(node, context) {
		visit_function(node, context);
	},
	FunctionExpression(node, context) {
		visit_function(node, context);
	},
	FunctionDeclaration(node, context) {
		visit_function(node, context);
	},

	Component(node, context) {
		context.state.component = node;

		if (node.params.length > 0) {
			const props = node.params[0];

			if (props.type === 'ObjectPattern') {
				const paths = extract_paths(props);

				for (const path of paths) {
					const name = /** @type {AST.Identifier} */ (path.node).name;
					const binding = context.state.scope.get(name);

					if (binding !== null) {
						binding.kind = path.has_default_value ? 'prop_fallback' : 'prop';

						binding.transform = {
							read: (_) => {
								return path.expression(b.id('__props'));
							},
							assign: (node, value) => {
								return b.assignment(
									'=',
									/** @type {AST.MemberExpression} */ (path.expression(b.id('__props'))),
									value,
								);
							},
							update: (node) =>
								b.update(node.operator, path.expression(b.id('__props')), node.prefix),
						};
					}
				}
			} else if (props.type === 'AssignmentPattern') {
				error(
					'Props are always an object, use destructured props with default values instead',
					context.state.analysis.module.filename,
					props,
					context.state.loose ? context.state.analysis.errors : undefined,
				);
			}
		}
		/** @type {AST.Element[]} */
		const elements = [];

		// Track metadata for this component
		const metadata = {
			await: false,
			styleClasses: /** @type {StyleClasses} */ (new Map()),
		};

		/** @type {TopScopedClasses} */
		const topScopedClasses = new Map();

		const control_flow_checks = create_control_flow_checks();

		context.next({
			...context.state,
			elements,
			function_depth: (context.state.function_depth ?? 0) + 1,
			metadata,
			control_flow_checks,
		});

		const css = node.css;

		if (css !== null) {
			// Analyze CSS to set global selector metadata
			analyze_css(css);

			for (const node of elements) {
				prune_css(css, node, metadata.styleClasses, topScopedClasses);
			}

			if (topScopedClasses.size > 0) {
				node.metadata.topScopedClasses = topScopedClasses;
			}

			if (metadata.styleClasses.size > 0) {
				node.metadata.styleClasses = metadata.styleClasses;

				for (const [className, property] of metadata.styleClasses) {
					if (!topScopedClasses?.has(className)) {
						error(
							`CSS class ".${className}" does not exist as a stand-alone class in ${node.id?.name ? node.id.name : "this component's"} <style> block`,
							context.state.analysis.module.filename,
							property,
							context.state.loose ? context.state.analysis.errors : undefined,
						);
					}
				}
			}
		}

		// Store component metadata in analysis
		// Only add metadata if component has a name (not anonymous)
		if (node.id) {
			context.state.analysis.component_metadata.push({
				id: node.id.name,
				async: metadata.await,
			});
		}
	},

	ForStatement(node, context) {
		if (is_inside_component(context)) {
			// TODO: it's a fatal error for now but
			// we could implement the for loop for the ts mode only
			error(
				'For loops are not supported in components. Use for...of instead.',
				context.state.analysis.module.filename,
				node,
			);
		}

		context.next();
	},

	SwitchStatement(node, context) {
		if (!is_inside_component(context)) {
			return context.next();
		}

		const { control_flow_checks } = context.state;

		context.visit(node.discriminant, context.state);

		for (const switch_case of node.cases) {
			if (switch_case.consequent.length === 0) {
				continue;
			}

			register_check(control_flow_checks, switch_case, ['template', 'await']);

			context.visit(switch_case, context.state);

			if (!is_check_satisfied(control_flow_checks, switch_case)) {
				error(
					'Component switch statements must contain a template or an await expression in each of their cases. Move the switch statement into an effect if it does not render anything.',
					context.state.analysis.module.filename,
					switch_case,
					context.state.loose ? context.state.analysis.errors : undefined,
				);
			}
		}
	},

	ForOfStatement(node, context) {
		if (!is_inside_component(context)) {
			return context.next();
		}

		if (node.index) {
			const state = context.state;
			const scope = /** @type {ScopeInterface} */ (state.scopes.get(node));
			const binding = scope.get(/** @type {AST.Identifier} */ (node.index).name);

			if (binding !== null) {
				binding.kind = 'index';
				binding.transform = {
					read: (node) => {
						return b.call('_$_.get', node);
					},
				};
			}
		}

		if (node.key) {
			const state = context.state;
			const pattern = /** @type {AST.VariableDeclaration} */ (node.left).declarations[0].id;
			const paths = extract_paths(pattern);
			const scope = /** @type {ScopeInterface} */ (state.scopes.get(node));
			/** @type {AST.Identifier | AST.Pattern} */
			let pattern_id;
			if (state.to_ts || state.mode === 'server') {
				pattern_id = pattern;
			} else {
				pattern_id = b.id(scope.generate('pattern'));
				/** @type {AST.VariableDeclaration} */ (node.left).declarations[0].id = pattern_id;
			}

			for (const path of paths) {
				const name = /** @type {AST.Identifier} */ (path.node).name;
				const binding = context.state.scope.get(name);

				if (binding !== null) {
					binding.kind = 'for_pattern';
					if (!binding.metadata) {
						binding.metadata = {
							pattern: /** @type {AST.Identifier} */ (pattern_id),
						};
					}

					binding.transform = {
						read: () => {
							return path.expression(b.call('_$_.get', /** @type {AST.Identifier} */ (pattern_id)));
						},
					};
				}
			}
		}

		const { control_flow_checks } = context.state;

		register_check(control_flow_checks, node.body, ['template', 'await']);

		context.next();

		if (!is_check_satisfied(control_flow_checks, node.body)) {
			error(
				'Component for...of loops must contain a template or an await expression in their body. Move the for loop into an effect if it does not render anything.',
				context.state.analysis.module.filename,
				node.body,
				context.state.loose ? context.state.analysis.errors : undefined,
			);
		}
	},

	ExportNamedDeclaration(node, context) {
		const server_block = context.state.ancestor_server_block;

		if (!server_block) {
			return context.next();
		}

		const exports = server_block.metadata.exports;
		const declaration = /** @type {AST.RippleExportNamedDeclaration} */ (node).declaration;

		if (declaration && declaration.type === 'FunctionDeclaration') {
			exports.add(declaration.id.name);
		} else if (declaration && declaration.type === 'Component') {
			error(
				'Not implemented: Exported component declaration not supported in server blocks.',
				context.state.analysis.module.filename,
				/** @type {AST.Identifier} */ (declaration.id),
				context.state.loose ? context.state.analysis.errors : undefined,
			);
			// TODO: the client and server rendering doesn't currently support components
			// If we're going to support this, we need to account also for anonymous object declaration
			// and specifiers
			// 	exports.add(/** @type {AST.Identifier} */ (declaration.id).name);
		} else if (declaration && declaration.type === 'VariableDeclaration') {
			for (const decl of declaration.declarations) {
				if (decl.init !== undefined && decl.init !== null) {
					if (decl.id.type === 'Identifier') {
						if (
							decl.init.type === 'FunctionExpression' ||
							decl.init.type === 'ArrowFunctionExpression'
						) {
							exports.add(decl.id.name);
							continue;
						} else if (decl.init.type === 'Identifier') {
							const name = decl.init.name;
							const binding = context.state.scope.get(name);
							if (binding && is_binding_function(binding, context.state.scope)) {
								exports.add(decl.id.name);
								continue;
							}
						} else if (decl.init.type === 'MemberExpression') {
							error(
								'Not implemented: Exported member expressions are not supported in server blocks.',
								context.state.analysis.module.filename,
								decl.init,
								context.state.loose ? context.state.analysis.errors : undefined,
							);
							continue;
						}
					} else if (decl.id.type === 'ObjectPattern' || decl.id.type === 'ArrayPattern') {
						const paths = extract_paths(decl.id);
						for (const path of paths) {
							error(
								'Not implemented: Exported object or array patterns are not supported in server blocks.',
								context.state.analysis.module.filename,
								path.node,
								context.state.loose ? context.state.analysis.errors : undefined,
							);
						}
					}
				}
				// TODO: allow exporting consts when hydration is supported
				error(
					`Not implemented: Exported '${decl.id.type}' type is not supported in server blocks.`,
					context.state.analysis.module.filename,
					decl,
					context.state.loose ? context.state.analysis.errors : undefined,
				);
			}
		} else if (node.specifiers) {
			for (const specifier of node.specifiers) {
				const name = /** @type {AST.Identifier} */ (specifier.local).name;
				const binding = context.state.scope.get(name);
				const is_function = binding && is_binding_function(binding, context.state.scope);

				if (is_function) {
					exports.add(name);
					continue;
				}

				error(
					`Not implemented: Exported specifier type not supported in server blocks.`,
					context.state.analysis.module.filename,
					specifier,
					context.state.loose ? context.state.analysis.errors : undefined,
				);
			}
		} else {
			error(
				'Not implemented: Exported declaration type not supported in server blocks.',
				context.state.analysis.module.filename,
				node,
				context.state.loose ? context.state.analysis.errors : undefined,
			);
		}

		return context.next();
	},

	TSTypeReference(node, context) {
		// bug in our acorn pasrer: it uses typeParameters instead of typeArguments
		// @ts-expect-error
		if (node.typeParameters) {
			// @ts-expect-error
			node.typeArguments = node.typeParameters;
			// @ts-expect-error
			delete node.typeParameters;
		}
		context.next();
	},

	ReturnStatement(node, context) {
		if (!is_inside_component(context)) {
			return context.next();
		}

		if (node.argument !== null && node.argument !== undefined) {
			error(
				'Component return statements must not have a return value',
				context.state.analysis.module.filename,
				node,
				context.state.loose ? context.state.analysis.errors : undefined,
			);
			return;
		}

		const condition_path = [];
		let found_if = false;
		/** @type {AST.IfStatement | AST.Element | null} */
		let containing_node = null;

		for (let i = context.path.length - 1; i >= 0; i -= 1) {
			const ancestor = context.path[i];
			if (ancestor.type === 'Component') {
				break;
			}
			if (ancestor.type === 'IfStatement') {
				found_if = true;
				condition_path.unshift(ancestor.test);
				containing_node = ancestor;
			}
			if (ancestor.type === 'Element' && !containing_node) {
				containing_node = ancestor;
			}
		}

		if (!found_if) {
			error(
				'Early return must be inside an if statement',
				context.state.analysis.module.filename,
				node,
				context.state.loose ? context.state.analysis.errors : undefined,
			);
			return;
		}

		const component = is_inside_component(context, true);
		if (component) {
			component.metadata.returns = component.metadata.returns || [];
			component.metadata.returns.push({
				node,
				condition_path,
				containing_node,
			});
		}

		mark_control_flow_has_return(context.path);
		satisfy_check(context.state.control_flow_checks, context.path, 'return');
	},

	IfStatement(node, context) {
		if (!is_inside_component(context)) {
			return context.next();
		}

		const { control_flow_checks, analysis, loose } = context.state;
		const filename = analysis.module.filename;
		const errors = loose ? analysis.errors : undefined;

		register_check(control_flow_checks, node.consequent, ['template', 'await', 'return']);

		context.visit(node.consequent, context.state);

		if (!is_check_satisfied(control_flow_checks, node.consequent)) {
			error(
				'Component if statements must contain a template in their "then" body. Move the if statement into an effect if it does not render anything.',
				filename,
				node.consequent,
				errors,
			);
		}

		check_unreachable_after_return(node.consequent, filename, errors);

		if (node.alternate) {
			register_check(control_flow_checks, node.alternate, ['template', 'await', 'return']);

			context.visit(node.alternate, context.state);

			if (!is_check_satisfied(control_flow_checks, node.alternate)) {
				error(
					'Component if statements must contain a template in their "else" body. Move the if statement into an effect if it does not render anything.',
					filename,
					node.alternate,
					errors,
				);
			}

			check_unreachable_after_return(node.alternate, filename, errors);
		}
	},

	TryStatement(node, context) {
		const { state } = context;
		if (!is_inside_component(context)) {
			return context.next();
		}

		if (node.pending) {
			if (state.metadata?.await === false) {
				state.metadata.await = true;
			}

			const { control_flow_checks } = state;

			register_check(control_flow_checks, node.block, ['template']);

			context.visit(node.block, state);

			if (!is_check_satisfied(control_flow_checks, node.block)) {
				error(
					'Component try statements must contain a template in their main body. Move the try statement into an effect if it does not render anything.',
					state.analysis.module.filename,
					node.block,
					context.state.loose ? context.state.analysis.errors : undefined,
				);
			}

			register_check(control_flow_checks, node.pending, ['template']);

			context.visit(node.pending, state);

			if (!is_check_satisfied(control_flow_checks, node.pending)) {
				error(
					'Component try statements must contain a template in their "pending" body. Rendering a pending fallback is required to have a template.',
					state.analysis.module.filename,
					node.pending,
					context.state.loose ? context.state.analysis.errors : undefined,
				);
			}
		}

		if (node.handler) {
			context.visit(node.handler, state);
		}

		if (node.finalizer) {
			context.visit(node.finalizer, state);
		}
	},

	ForInStatement(node, context) {
		if (is_inside_component(context)) {
			// TODO: it's a fatal error for now but
			// we could implement the for in loop for the ts mode only to make it a usage error
			error(
				'For...in loops are not supported in components. Use for...of instead.',
				context.state.analysis.module.filename,
				node,
			);
		}

		context.next();
	},

	JSXElement(node, context) {
		const inside_tsx_compat = context.path.some((n) => n.type === 'TsxCompat');

		if (inside_tsx_compat) {
			return context.next();
		}
		// TODO: could compile it as something to avoid a fatal error
		error(
			'Elements cannot be used as generic expressions, only as statements within a component',
			context.state.analysis.module.filename,
			node,
		);
	},

	TsxCompat(_, context) {
		satisfy_check(context.state.control_flow_checks, context.path, 'template');
		return context.next();
	},

	Element(node, context) {
		if (!is_inside_component(context)) {
			error(
				'Elements cannot be used outside of components',
				context.state.analysis.module.filename,
				node,
			);
		}

		const { state, visit, path } = context;
		const is_dom_element = is_element_dom_element(node);
		const attribute_names = new Set();

		satisfy_check(context.state.control_flow_checks, path, 'template');

		validate_nesting(node, context);

		// Store capitalized name for dynamic components/elements
		// TODO: this is not quite right as the node.id could be a member expression
		// so, we'd need to identify dynamic based on that too
		// However, we're going to get rid of capitalization in favor of jsx()
		// so, this will be need to be redone.
		if (node.id.type === 'Identifier' && node.id.tracked) {
			const source_name = node.id.name;
			const capitalized_name = source_name.charAt(0).toUpperCase() + source_name.slice(1);
			node.metadata.ts_name = capitalized_name;
			node.metadata.source_name = source_name;

			// Mark the binding as a dynamic component so we can capitalize it everywhere
			const binding = context.state.scope.get(source_name);
			if (binding) {
				if (!binding.metadata) {
					binding.metadata = {};
				}
				binding.metadata.is_dynamic_component = true;
			}

			if (!is_dom_element && state.elements) {
				state.elements.push(node);
				// Mark dynamic elements as scoped by default since we can't match CSS at compile time
				if (state.component?.css) {
					node.metadata.scoped = true;
				}
			}
		}

		if (is_dom_element) {
			if (/** @type {AST.Identifier} */ (node.id).name === 'head') {
				// head validation
				if (node.attributes.length > 0) {
					// TODO: could transform attributes as something, e.g. Text Node, and avoid a fatal error
					error('<head> cannot have any attributes', state.analysis.module.filename, node);
				}
				if (node.children.length === 0) {
					// TODO: could transform children as something, e.g. Text Node, and avoid a fatal error
					error('<head> must have children', state.analysis.module.filename, node);
				}

				for (const child of node.children) {
					context.visit(child, { ...state, inside_head: true });
				}

				return;
			}
			if (state.inside_head) {
				if (/** @type {AST.Identifier} */ (node.id).name === 'title') {
					const children = normalize_children(node.children, context);

					if (children.length !== 1 || children[0].type !== 'Text') {
						// TODO: could transform children as something, e.g. Text Node, and avoid a fatal error
						error(
							'<title> must have only contain text nodes',
							state.analysis.module.filename,
							node,
						);
					}
				}

				// check for invalid elements in head
				if (!valid_in_head.has(/** @type {AST.Identifier} */ (node.id).name)) {
					// TODO: could transform invalid elements as something, e.g. Text Node, and avoid a fatal error
					error(
						`<${/** @type {AST.Identifier} */ (node.id).name}> cannot be used in <head>`,
						state.analysis.module.filename,
						node,
					);
				}
			} else {
				if (/** @type {AST.Identifier} */ (node.id).name === 'script') {
					const err_msg = '<script> cannot be used outside of <head>.';
					error(
						err_msg,
						state.analysis.module.filename,
						node.openingElement,
						state.loose ? state.analysis.errors : undefined,
					);

					if (node.closingElement) {
						error(
							err_msg,
							state.analysis.module.filename,
							node.closingElement,
							state.loose ? state.analysis.errors : undefined,
						);
					}
				}
			}

			const is_void = is_void_element(/** @type {AST.Identifier} */ (node.id).name);

			if (state.elements) {
				state.elements.push(node);
			}

			for (const attr of node.attributes) {
				if (attr.type === 'Attribute') {
					if (attr.value && attr.value.type === 'JSXEmptyExpression') {
						const value = /** @type {ESTreeJSX.JSXEmptyExpression & AST.NodeWithLocation} */ (
							attr.value
						);
						error(
							'attributes must only be assigned a non-empty expression',
							state.analysis.module.filename,
							{
								...value,
								start: value.start - 1,
								end: value.end + 1,
								loc: {
									start: {
										line: value.loc.start.line,
										column: value.loc.start.column - 1,
									},
									end: {
										line: value.loc.end.line,
										column: value.loc.end.column + 1,
									},
								},
							},
							context.state.loose ? context.state.analysis.errors : undefined,
						);
					}
					if (attr.name.type === 'Identifier') {
						attribute_names.add(attr.name);

						if (attr.name.name === 'key') {
							error(
								'The `key` attribute is not a thing in Ripple, and cannot be used on DOM elements. If you are using a for loop, then use the `for (let item of items; key item.id)` syntax.',
								state.analysis.module.filename,
								attr,
								context.state.loose ? context.state.analysis.errors : undefined,
							);
						}

						if (is_event_attribute(attr.name.name)) {
							const handler = visit(/** @type {AST.Expression} */ (attr.value), state);
							const is_delegated = is_delegated_event(attr.name.name, handler, context);

							if (is_delegated) {
								if (attr.metadata === undefined) {
									attr.metadata = { path: [...path] };
								}

								attr.metadata.delegated = is_delegated;
							}
						} else if (attr.value !== null) {
							visit(attr.value, state);
						}
					}
				}
			}

			if (is_void && node.children.length > 0) {
				error(
					`The <${/** @type {AST.Identifier} */ (node.id).name}> element is a void element and cannot have children`,
					state.analysis.module.filename,
					node,
					context.state.loose ? context.state.analysis.errors : undefined,
				);
			}
		} else {
			for (const attr of node.attributes) {
				if (attr.type === 'Attribute') {
					if (attr.name.type === 'Identifier') {
						attribute_names.add(attr.name);
					}
					if (attr.value !== null) {
						visit(attr.value, state);
					}
				} else if (attr.type === 'SpreadAttribute') {
					visit(attr.argument, state);
				} else if (attr.type === 'RefAttribute') {
					visit(attr.argument, state);
				}
			}
			/** @type {(AST.Node | AST.Expression)[]} */
			let implicit_children = [];
			/** @type {AST.Identifier[]} */
			let explicit_children = [];

			for (const child of node.children) {
				if (child.type === 'Component') {
					if (child.id?.name === 'children') {
						explicit_children.push(child.id);
					}
				} else if (child.type !== 'EmptyStatement') {
					implicit_children.push(
						child.type === 'Text' || child.type === 'Html' ? child.expression : child,
					);
				}
			}

			if (implicit_children.length > 0 && explicit_children.length > 0) {
				for (const item of [...explicit_children, ...implicit_children]) {
					error(
						'Cannot have both implicit and explicit children',
						state.analysis.module.filename,
						item,
						context.state.loose ? context.state.analysis.errors : undefined,
					);
				}
			}
		}

		// Validation
		for (const attribute of attribute_names) {
			const name = attribute.name;
			if (name === 'children') {
				if (is_dom_element) {
					error(
						'Cannot have a `children` prop on an element',
						state.analysis.module.filename,
						attribute,
						context.state.loose ? context.state.analysis.errors : undefined,
					);
				}
			}
		}

		return {
			...node,
			children: node.children.map((child) => visit(child)),
		};
	},

	Text(node, context) {
		satisfy_check(context.state.control_flow_checks, context.path, 'template');
		context.next();
	},

	AwaitExpression(node, context) {
		const parent_block = get_parent_block_node(context);

		if (is_inside_component(context)) {
			if (context.state.metadata?.await === false) {
				context.state.metadata.await = true;
			}

			if (
				parent_block !== null &&
				parent_block?.type !== 'Component' &&
				!context.state.ancestor_server_block &&
				!(
					parent_block.type === 'TryStatement' &&
					parent_block.pending &&
					is_inside_try_block(parent_block, context)
				)
			) {
				// we want the error to live on the `await` keyword vs the whole expression
				const adjusted_node /** @type {AST.AwaitExpression} */ = {
					...node,
					end: /** @type {AST.NodeWithLocation} */ (node).start + 'await'.length,
				};
				error(
					'`await` is not allowed in client-side control-flow statements',
					context.state.analysis.module.filename,
					adjusted_node,
					context.state.loose ? context.state.analysis.errors : undefined,
				);
			}
		}

		if (parent_block) {
			if (!parent_block.metadata) {
				parent_block.metadata = { path: [...context.path] };
			}
			parent_block.metadata.has_await = true;
		}

		satisfy_check(context.state.control_flow_checks, context.path, 'await');

		context.next();
	},
};

/**
 *
 * @param {AST.Program} ast
 * @param {string} filename
 * @param {AnalyzeOptions} options
 * @returns {AnalysisResult}
 */
export function analyze(ast, filename, options = {}) {
	const scope_root = new ScopeRoot();

	const { scope, scopes } = create_scopes(ast, scope_root, null);

	const analysis = /** @type {AnalysisResult} */ ({
		module: { ast, scope, scopes, filename },
		ast,
		scope,
		scopes,
		component_metadata: [],
		metadata: {
			serverIdentifierPresent: false,
		},
		errors: options.errors ?? [],
		comments: options.comments ?? [],
	});

	walk(
		ast,
		/** @type {AnalysisState} */
		{
			scope,
			scopes,
			analysis,
			inside_head: false,
			ancestor_server_block: undefined,
			to_ts: options.to_ts ?? false,
			loose: options.loose ?? false,
			metadata: {},
			mode: options.mode,
		},
		visitors,
	);

	return analysis;
}
