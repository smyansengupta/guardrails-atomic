import { Specification, SpecificationSchema } from '@/lib/types/specification';
import { SpecificationError } from '@/lib/utils/errors';
import YAML from 'yaml';
import { ZodError } from 'zod';

/**
 * Parse and validate YAML specification
 *
 * @param yamlString - The YAML specification as a string
 * @returns Parsed and validated Specification object
 * @throws SpecificationError if YAML is invalid or doesn't match schema
 */
export function parseSpec(yamlString: string): Specification {
  try {
    // 1. Parse YAML string
    const parsed = YAML.parse(yamlString);

    if (!parsed) {
      throw new SpecificationError('YAML is empty or invalid');
    }

    // 2. Validate against Zod schema
    const spec = SpecificationSchema.parse(parsed);

    return spec;
  } catch (error) {
    // 3. Handle parsing errors gracefully with helpful messages
    if (error instanceof YAML.YAMLParseError) {
      throw new SpecificationError(
        `YAML parsing failed at line ${error.linePos?.[0]?.line}: ${error.message}`
      );
    }

    if (error instanceof ZodError) {
      const errorMessages = error.issues.map((err) => {
        const path = err.path.join('.');
        return `  - ${path}: ${err.message}`;
      });

      throw new SpecificationError(
        `Validation failed:\n${errorMessages.join('\n')}`
      );
    }

    if (error instanceof SpecificationError) {
      throw error;
    }

    throw new SpecificationError(
      `Unknown error during spec parsing: ${error instanceof Error ? error.message : String(error)}`
    );
  }
}
